import Lean.CompactedRegion
import Lean.Data.Json
import LeanReach.Query.Ilean
import LeanReach.SourceIndex.Types

namespace LeanReach.SourceIndex

open Lean

private abbrev CacheFingerprint := Array (Name × String)
private abbrev CachePayload := Nat × CacheFingerprint × Index

private def cacheVersion : Nat := 3
private def buildBatchSize : Nat := 32
private def buildWorkerCount : Nat := 8

private structure Builder where
  declarations : NameMap (Name × Lsp.Range) := {}
  downstream : NameMap NameSet := {}

private def normalizeRoots (roots : Array Name) : Array Name :=
  (NameSet.ofArray roots).toArray

private def addIlean (builder : Builder) (ilean : Server.Ilean) : Builder := Id.run do
  let mut builder := builder
  let moduleString := Query.nameString ilean.module

  for (declarationName, range) in ilean.decls do
    let declarations :=
      builder.declarations.insert declarationName.toName (ilean.module, range.selectionRange)
    builder := { builder with declarations }

  for (ident, info) in ilean.references do
    let .const definitionModule declarationName := ident | continue
    let declaration := declarationName.toName
    if definitionModule == moduleString && !builder.declarations.contains declaration then
      if let some location := info.definition? then
        let declarations :=
          builder.declarations.insert declaration (ilean.module, location.range)
        builder := { builder with declarations }
    for usage in info.usages do
      let some parentName := usage.parentDecl? | continue
      let downstream :=
        builder.downstream.alter declaration fun parents? =>
          some ((parents?.getD {}).insert parentName.toName)
      builder := { builder with downstream }

  return builder

private def buildDownstream (declarations : Array Declaration)
    (nameToId : NameMap DeclId) (relations : NameMap NameSet) : Adjacency := Id.run do
  let mut offsets := Array.replicate (declarations.size + 1) 0
  let mut edges := #[]
  for declarationId in [:declarations.size] do
    offsets := offsets.set! declarationId edges.size
    if let some parents := relations.find? declarations[declarationId]!.name then
      for parent in parents do
        if let some parentId := nameToId.find? parent then
          edges := edges.push parentId
  offsets := offsets.set! declarations.size edges.size
  return { offsets, edges }

private def transpose (size : Nat) (adjacency : Adjacency) : Adjacency := Id.run do
  let mut counts := Array.replicate size 0
  for target in adjacency.edges do
    counts := counts.set! target (counts[target]! + 1)

  let mut offsets := Array.replicate (size + 1) 0
  for declarationId in [:size] do
    offsets := offsets.set! (declarationId + 1)
      (offsets[declarationId]! + counts[declarationId]!)

  let mut cursors := offsets.extract 0 size
  let mut edges := Array.replicate adjacency.edges.size 0
  for source in [:size] do
    for target in adjacency.neighbors source do
      let cursor := cursors[target]!
      edges := edges.set! cursor source
      cursors := cursors.set! target (cursor + 1)
  return { offsets, edges }

private def Builder.finalize (builder : Builder) : Index := Id.run do
  let mut declarations := #[]
  let mut nameToId := {}
  for (name, moduleName, range) in builder.declarations do
    nameToId := nameToId.insert name declarations.size
    declarations := declarations.push {
      name
      lowerName := (Query.nameString name).toLower
      module := moduleName
      range
    }
  let downstream := buildDownstream declarations nameToId builder.downstream
  return {
    declarations
    nameToId
    upstream := transpose declarations.size downstream
    downstream
  }

private def loadChunk (modules : Array Name) :
    IO (Array (Name × Option Server.Ilean)) :=
  modules.mapM fun moduleName => do
    return (moduleName, ← Query.loadIlean? moduleName)

private def loadBatch (modules : Array Name) :
    IO (Array (Name × Option Server.Ilean)) := do
  if modules.isEmpty then
    return #[]
  let workerCount := min buildWorkerCount modules.size
  let chunkSize := (modules.size + workerCount - 1) / workerCount
  let tasks ← (Array.range workerCount).mapM fun worker => do
    let start := worker * chunkSize
    let stop := min (start + chunkSize) modules.size
    IO.asTask (loadChunk (modules.extract start stop))
  let chunks ← tasks.mapM fun task => do
    return ← IO.wait task
  let chunks ← chunks.mapM fun
    | Except.ok chunk => pure chunk
    | Except.error error =>
      throw error
  return chunks.flatten

/-- Build a source-visible declaration and direct-reference index without importing an Environment. -/
def build (requestedRoots : Array Name) : IO Index := do
  let requestedRoots := normalizeRoots requestedRoots
  if requestedRoots.isEmpty then
    throw <| IO.userError "source index needs at least one root module"
  -- Lean implicitly imports `Init` unless a module uses `prelude`; `.ilean` records only explicit
  -- imports, so include the standard prelude closure explicitly.
  let roots := normalizeRoots (requestedRoots.push `Init)
  let mut queue := roots
  let mut visited := NameSet.ofArray roots
  let mut offset := 0
  let mut builder : Builder := {}
  while offset < queue.size do
    let stop := min (offset + buildBatchSize) queue.size
    let batch := queue.extract offset stop
    for (moduleName, ilean?) in (← loadBatch batch) do
      let some ilean := ilean? |
        throw <| IO.userError
          s!"missing .ilean for module {Query.nameString moduleName}"
      if ilean.version != 5 then
        throw <| IO.userError
          s!"unsupported .ilean version {ilean.version} for {Query.nameString moduleName}"
      builder := addIlean builder ilean
      for imported in ilean.directImports do
        let importedName := imported.module.toName
        unless visited.contains importedName do
          visited := visited.insert importedName
          queue := queue.push importedName
    offset := stop
  return builder.finalize

private def readModuleDepHash? (moduleName : Name) : IO (Option String) := do
  try
    let tracePath := (← findOLean moduleName).withExtension "trace"
    if !(← tracePath.pathExists) then
      return none
    match Json.parse (← IO.FS.readFile tracePath) with
    | .ok json => return (json.getObjValAs? String "depHash").toOption
    | .error _ => return none
  catch _ =>
    return none

private def cacheFingerprint? (roots : Array Name) : IO (Option CacheFingerprint) := do
  let mut fingerprint := #[]
  for root in roots do
    let some depHash ← readModuleDepHash? root | return none
    fingerprint := fingerprint.push (root, depHash)
  return some fingerprint

private def fingerprintHash (fingerprint : CacheFingerprint) : UInt64 :=
  fingerprint.foldl (init := 7) fun state (moduleName, depHash) =>
    mixHash state (mixHash (hash moduleName) (hash depHash))

private def rootSetHash (roots : Array Name) : UInt64 :=
  roots.foldl (init := 7) fun state moduleName =>
    mixHash state (hash moduleName)

private def cachePath (roots : Array Name) : IO System.FilePath := do
  let cwd ← IO.Process.getCurrentDir
  let rootLabel := Query.nameString roots[0]!
  let rootLabel :=
    if roots.size == 1 then rootLabel
    else s!"{rootLabel}-{rootSetHash roots}"
  return cwd / ".lake" / "leanreach" /
    s!"{rootLabel}-v{cacheVersion}.index"

private def cacheKey (fingerprint : CacheFingerprint) : Name :=
  Name.str `LeanReach.sourceIndex (toString (fingerprintHash fingerprint))

private unsafe def readCache? (path : System.FilePath) (expected : CacheFingerprint) :
    IO (Option (Index × CompactedRegion)) := do
  if !(← path.pathExists) then
    return none
  try
    let (payload, region) ←
      unsafe CompactedRegion.read (α := CachePayload) path #[]
    let (version, storedFingerprint, index) := payload
    if version == cacheVersion && storedFingerprint == expected then
      return some (index, region)
    unsafe region.free
    return none
  catch _ =>
    return none

private unsafe def writeCache (path : System.FilePath) (fingerprint : CacheFingerprint)
    (index : Index) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let payload : CachePayload := (cacheVersion, fingerprint, index)
  let _ ← unsafe CompactedRegion.save path (cacheKey fingerprint) payload #[] none

/--
Restore a valid source index or build and best-effort persist one. `log` receives cache lifecycle
messages and is silent by default.
-/
private unsafe def load (roots : Array Name) (log : String → IO Unit) :
    IO (Index × Option CompactedRegion) := do
  let roots := normalizeRoots roots
  if roots.isEmpty then
    throw <| IO.userError "source index needs at least one root module"
  let fingerprint? ← cacheFingerprint? roots
  if let some fingerprint := fingerprint? then
    let path ← cachePath roots
    if let some (index, region) ← unsafe readCache? path fingerprint then
      log s!"source index restored: {path}"
      return (index, some region)
    log s!"source index cache miss: {path}"
    let index ← build roots
    try
      unsafe writeCache path fingerprint index
      log s!"source index saved: {path}"
    catch error =>
      log s!"source index cache write failed: {error}"
    return (index, none)
  log "source index cache disabled: a root module has no Lake depHash"
  return (← build roots, none)

/--
Load an index for one action and release any mapped compacted region afterwards. The action must
materialize its result instead of returning values that share storage with the index.
-/
unsafe def withIndex {α : Type} (roots : Array Name)
    (action : Index → IO α) (log : String → IO Unit := fun _ => pure ()) : IO α := do
  let (index, region?) ← unsafe load roots log
  try
    action index
  finally
    if let some region := region? then
      unsafe region.free

end LeanReach.SourceIndex
