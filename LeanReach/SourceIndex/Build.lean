import Lean.Data.Json
import LeanReach.Query.Ilean
import LeanReach.SourceIndex.Types

namespace LeanReach.SourceIndex

open Lean

private abbrev CacheFingerprint := Array (Name × String)
private abbrev CachePayload := Nat × CacheFingerprint × Index

private def cacheVersion : Nat := 1
private def cacheKey : Name := `LeanReach.sourceIndexV1
private def buildBatchSize : Nat := 64
private def buildWorkerCount : Nat := 8

def normalizeRoots (roots : Array Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut result := #[]
  for root in roots.qsort Name.quickLt do
    unless seen.contains root do
      seen := seen.insert root
      result := result.push root
  return result

private def declarationOfLocation (moduleName : Name)
    (location : Lsp.RefInfo.Location) : Declaration where
  module := moduleName
  range := {
    rangeStartPosLine := location.startPosLine
    rangeStartPosCharacter := location.startPosCharacter
    rangeEndPosLine := location.endPosLine
    rangeEndPosCharacter := location.endPosCharacter
    selectionRangeStartPosLine := location.startPosLine
    selectionRangeStartPosCharacter := location.startPosCharacter
    selectionRangeEndPosLine := location.endPosLine
    selectionRangeEndPosCharacter := location.endPosCharacter
  }

private def insertParent (downstream : NameMap NameSet) (dependency parent : Name) :
    NameMap NameSet :=
  downstream.insert dependency ((downstream.find? dependency).getD {} |>.insert parent)

private def addIlean (index : Index) (ilean : Server.Ilean) : Index := Id.run do
  let mut declarations := index.declarations
  let mut downstream := index.downstream
  let moduleString := Query.nameString ilean.module

  for (declarationName, range) in ilean.decls do
    declarations := declarations.insert declarationName.toName {
      module := ilean.module
      range
    }

  for (ident, info) in ilean.references do
    let .const definitionModule declarationName := ident | continue
    let declaration := declarationName.toName
    if definitionModule == moduleString && !declarations.contains declaration then
      if let some location := info.definition? then
        declarations := declarations.insert declaration
          (declarationOfLocation ilean.module location)
    for usage in info.usages do
      let some parentName := usage.parentDecl? | continue
      downstream := insertParent downstream declaration parentName.toName

  return { declarations, downstream }

private def loadChunk (modules : Array Name) :
    IO (Array (Name × Option Server.Ilean)) := do
  let mut results := #[]
  for moduleName in modules do
    results := results.push (moduleName, ← Query.loadIlean? moduleName)
  return results

private def loadBatch (modules : Array Name) :
    IO (Array (Name × Option Server.Ilean)) := do
  if modules.isEmpty then
    return #[]
  let workerCount := min buildWorkerCount modules.size
  let chunkSize := (modules.size + workerCount - 1) / workerCount
  let mut tasks : Array (Task
    (Except IO.Error (Array (Name × Option Server.Ilean)))) := #[]
  for worker in [0:workerCount] do
    let start := worker * chunkSize
    let stop := min (start + chunkSize) modules.size
    tasks := tasks.push (← IO.asTask (loadChunk (modules.extract start stop)))
  let mut results := #[]
  let mut firstError? : Option IO.Error := none
  for task in tasks do
    match ← IO.wait task with
    | .ok chunk => results := results ++ chunk
    | .error error =>
      if firstError?.isNone then
        firstError? := some error
  match firstError? with
  | some error => throw error
  | none => return results

/-- Build a source-visible declaration and direct-reference index without importing an Environment. -/
def build (roots : Array Name) : IO Index := do
  let roots := normalizeRoots roots
  if roots.isEmpty then
    throw <| IO.userError "source index needs at least one root module"
  let mut queue := roots
  let mut visited := NameSet.ofArray roots
  let mut offset := 0
  let mut index : Index := {}
  while offset < queue.size do
    let stop := min (offset + buildBatchSize) queue.size
    let batch := queue.extract offset stop
    for (moduleName, ilean?) in (← loadBatch batch) do
      let some ilean := ilean? | continue
      if ilean.version != 5 then
        throw <| IO.userError
          s!"unsupported .ilean version {ilean.version} for {Query.nameString moduleName}"
      index := addIlean index ilean
      for imported in ilean.directImports do
        let importedName := imported.module.toName
        unless visited.contains importedName do
          visited := visited.insert importedName
          queue := queue.push importedName
    offset := stop
  return index

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

private def cachePath (roots : Array Name) (fingerprint : CacheFingerprint) :
    IO System.FilePath := do
  let cwd ← IO.Process.getCurrentDir
  let rootLabel := Query.nameString roots[0]!
  let hashLabel := fingerprint[0]!.2
  return cwd / ".lake" / "leanreach" /
    s!"{rootLabel}-{hashLabel}-v{cacheVersion}.index"

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
  let _ ← unsafe CompactedRegion.save path cacheKey payload #[] none

/--
Restore a valid source index or build and best-effort persist one. `log` receives cache lifecycle
messages and is silent by default.
-/
unsafe def load (roots : Array Name) (log : String → IO Unit := fun _ => pure ()) :
    IO Loaded := do
  let roots := normalizeRoots roots
  if roots.isEmpty then
    throw <| IO.userError "source index needs at least one root module"
  let fingerprint? ← cacheFingerprint? roots
  if let some fingerprint := fingerprint? then
    let path ← cachePath roots fingerprint
    if let some (index, region) ← unsafe readCache? path fingerprint then
      log s!"source index restored: {path}"
      return { index, region? := some region }
    log s!"source index cache miss: {path}"
    let index ← build roots
    try
      unsafe writeCache path fingerprint index
      log s!"source index saved: {path}"
    catch error =>
      log s!"source index cache write failed: {error}"
    return { index }
  log "source index cache disabled: a root module has no Lake depHash"
  return { index := ← build roots }

end LeanReach.SourceIndex
