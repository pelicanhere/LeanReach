import Lake.Build.Trace
import Lean.Environment
import Lean.Util.Path
import LeanReach.BlackListed
import LeanReach.Declaration
import LeanReach.Index
import LeanReach.ModuleData
import LeanReach.SourceInfo

namespace LeanReach.Cache

open Lean

private def catalogVersion := 6
private def relationsVersion := 7
private def fragmentVersion := 6
private def ppVersion := 3
private def rootHashVersion := 1

structure ModuleFragment where
  imports : Array Name
  declarations : Array (Name × NameSet)

/-- Save a compacted Lean object. Adapted from Loogle's `Pickle` module. -/
def pickle {α : Type} (path : System.FilePath) (value : α) (key : Name) : IO Unit :=
  saveModuleData path key (unsafe unsafeCast value)

private unsafe def unpickle (α : Type) (path : System.FilePath) :
    IO (α × CompactedRegion) := do
  let (value, region) ← readModuleData path
  return (unsafeCast value, region)

unsafe def loadPart (α : Type) (path : System.FilePath) (depHash : String) :
    IO (Option α) := do
  unless ← path.pathExists do return none
  try
    let ((storedHash, value), _) ← unsafe unpickle (String × α) path
    if storedHash == depHash then return some value
  catch _ => pure ()
  return none

private def depHash? (olean : System.FilePath) : IO (Option String) := do
  let path := olean.withExtension "trace"
  if ← path.pathExists then
    return (Json.parse (← IO.FS.readFile path) >>= (·.getObjValAs? String "depHash")).toOption
  let mut hashes := #[]
  for level in #[OLeanLevel.exported, OLeanLevel.server, OLeanLevel.private] do
    let path := level.adjustFileName olean
    if ← path.pathExists then
      hashes := hashes.push (toString (← Lake.computeFileHash path))
  return if hashes.isEmpty then none else some (String.intercalate ":" hashes.toList)

private def collapseInternal (internal : NameMap NameSet) (dependencies : NameSet) : NameSet :=
  Id.run do
    let mut pending : Array Name := #[]
    for dependency in dependencies do pending := pending.push dependency
    let mut seen : NameHashSet := {}
    let mut result : NameSet := {}
    while let some name := pending.back? do
      pending := pending.pop
      unless seen.contains name do
        seen := seen.insert name
        match internal.find? name with
        | some dependencies =>
          for dependency in dependencies do pending := pending.push dependency
        | none => result := result.insert name
    return result

private unsafe def readFragment (moduleName : Name) (olean : System.FilePath) :
    IO (ModuleFragment × Array CompactedRegion) := do
  let (parts, visibleIndex) ← unsafe ModuleData.readParts olean
  let some (all, _) := parts.back? |
    throw <| IO.userError s!"empty module data for '{moduleName}'"
  let some (visible, _) := parts[visibleIndex]? |
    throw <| IO.userError s!"missing visible module data for '{moduleName}'"
  let source ← sourceNames olean
  let visibleNames := visible.constants.foldl (init := ({} : NameHashSet))
    fun names info => names.insert info.name
  let (constants, internal) := all.constants.foldl
      (init := (({} : NameMap ConstantInfo), ({} : NameMap NameSet))) fun state info =>
    let constants := state.1.insert info.name info
    let internal :=
      if isBlackListed info.name || !visibleNames.contains info.name then
        state.2.insert info.name info.getUsedConstantsAsSet
      else state.2
    (constants, internal)
  return ({
    imports := all.imports.map (·.module)
    declarations := visible.constants.filterMap fun visibleInfo =>
      let name := visibleInfo.name
      if source.contains name.toString && !isBlackListed name then
        let info := (constants.find? name).getD visibleInfo
        some (name, collapseInternal internal info.getUsedConstantsAsSet)
      else none
  }, parts.map (·.2))

private unsafe def writeFragment (moduleName : Name) (olean path : System.FilePath)
    (hash : String) : IO Unit := do
  let regions ← show IO (Array CompactedRegion) from do
    let (fragment, regions) ← readFragment moduleName olean
    pickle path (hash, fragment) moduleName
    return regions
  regions.forM CompactedRegion.free

private unsafe def loadFragment (moduleName : Name) : IO ModuleFragment := do
  let olean ← findOLean moduleName
  let hash? ← depHash? olean
  let path := olean.withExtension s!"leanreach-module-{fragmentVersion}"
  if let some hash := hash? then
    if let some fragment ← unsafe loadPart ModuleFragment path hash then return fragment
    try
      writeFragment moduleName olean path hash
      if let some fragment ← unsafe loadPart ModuleFragment path hash then return fragment
    catch _ => pure ()
  return (← readFragment moduleName olean).1

unsafe def moduleNames (moduleName : Name) : IO (Array Name) :=
  return (← unsafe loadFragment moduleName).declarations.map (·.1)

unsafe def moduleDeclarations (moduleName : Name) :
    IO (Array (Name × NameSet)) :=
  return (← unsafe loadFragment moduleName).declarations

private unsafe def buildIndex (roots : Array Name) : IO Index := do
  let mut pending := roots
  let mut seen : NameHashSet := {}
  let mut declarations := #[]
  while !pending.isEmpty do
    let mut batch := #[]
    while batch.size < 32 do
      let some moduleName := pending.back? | break
      pending := pending.pop
      unless seen.contains moduleName do
        seen := seen.insert moduleName
        batch := batch.push moduleName
    let tasks ← batch.mapM fun moduleName => IO.asTask (unsafe loadFragment moduleName)
    for (moduleName, task) in batch.zip tasks do
      let fragment ← IO.ofExcept task.get
      pending := pending ++ fragment.imports
      for (name, dependencies) in fragment.declarations do
        declarations := declarations.push (name, moduleName, dependencies)
  return Index.build declarations

private def rootStamp (olean : System.FilePath) : IO String := do
  let trace := olean.withExtension "trace"
  let mut paths := #[]
  if ← trace.pathExists then
    paths := paths.push trace
  else
    for level in #[OLeanLevel.exported, OLeanLevel.server, OLeanLevel.private] do
      let path := level.adjustFileName olean
      if ← path.pathExists then paths := paths.push path
  let stamps ← paths.mapM fun path => do
    let metadata ← path.metadata
    return s!"{path}:{metadata.modified.sec}:{metadata.modified.nsec}:{metadata.byteSize}"
  return String.intercalate "|" stamps.toList

unsafe def rootData (roots : Array Name) : IO (System.FilePath × String × Name) := do
  let some root := roots[0]? | throw <| IO.userError "no root modules"
  let oleans ← roots.mapM findOLean
  let olean := oleans[0]!
  let stamps ← oleans.mapM rootStamp
  let stamp := String.intercalate "\u0001" <| (roots.zip stamps).toList.map fun (name, value) =>
    s!"{name}\t{value}"
  let cache := olean.withExtension s!"leanreach-root-hash-{rootHashVersion}"
  if ← cache.pathExists then
    try
      let storedStamp :: depHash :: _ := (← IO.FS.readFile cache).splitOn "\n" | pure ()
      if storedStamp == stamp then return (olean, depHash, root)
    catch _ => pure ()
  let hashes ← (roots.zip oleans).mapM fun (name, path) => do
    let some hash ← depHash? path |
      throw <| IO.userError s!"could not hash root module '{name}'"
    return s!"{name}:{hash}"
  let depHash := String.intercalate ":" hashes.toList
  try IO.FS.writeFile cache (stamp ++ "\n" ++ depHash)
  catch _ => pure ()
  return (olean, depHash, root)

unsafe def loadIndex (roots : Array Name) (loadRelations := true) : IO Index := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "leanreach" else "leanreach-roots"
  let catalogPath := olean.withExtension s!"{stem}-catalog-{catalogVersion}"
  let relationsPath := olean.withExtension s!"{stem}-relations-{relationsVersion}"
  if let some catalog ← unsafe loadPart Catalog catalogPath depHash then
    if !loadRelations then return Index.ofParts catalog default
    if let some relations ← unsafe loadPart Relations relationsPath depHash then
      return Index.ofParts catalog relations
  let index ← buildIndex roots
  try
    pickle catalogPath (depHash, index.catalog) (Name.str root "_leanreachCatalog")
    pickle relationsPath (depHash, index.relations) (Name.str root "_leanreachRelations")
  catch _ => IO.eprintln "leanreach: could not write root index cache"
  if loadRelations then return index
  return Index.ofParts index.catalog default

unsafe def loadPPModule (moduleName : Name) : IO (NameMap Declaration) := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return {}
  let path := olean.withExtension s!"leanreach-pp-{ppVersion}"
  return (← unsafe loadPart (NameMap Declaration) path depHash).getD {}

private unsafe def ppRootData (roots : Array Name) (suffix : String) :
    IO (System.FilePath × String × Name) := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "root" else "roots"
  return (
    olean.withExtension s!"leanreach-pp-{stem}-{suffix}",
    depHash,
    root
  )

unsafe def isFullyPP (roots : Array Name) : IO Bool := do
  let (path, depHash, _) ← unsafe ppRootData roots (toString ppVersion)
  return (← unsafe loadPart Bool path depHash).getD false

unsafe def loadPP (moduleOf? : Name → Option Name)
    (names : Array Name) : IO (NameMap Declaration) := do
  let mut byModule : NameMap (Array Name) := {}
  for name in names do
    if let some moduleName := moduleOf? name then
      byModule := byModule.insert moduleName
        ((byModule.find? moduleName).getD #[] |>.push name)
  let mut declarations := {}
  for (moduleName, names) in byModule do
    let cached ← unsafe loadPPModule moduleName
    for name in names do
      if let some declaration := cached.find? name then
        declarations := declarations.insert name declaration
  return declarations

unsafe def savePPModule (moduleName : Name) (declarations : NameMap Declaration) :
    IO Unit := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return
  let path := olean.withExtension s!"leanreach-pp-{ppVersion}"
  pickle path (depHash, declarations) (Name.str moduleName "_leanreachPP")

unsafe def savePP (before after : NameMap Declaration) : IO Unit := do
  let mut additions : NameMap (NameMap Declaration) := {}
  for (name, declaration) in after do
    unless before.contains name do
      let moduleName := declaration.moduleName.toName
      let moduleDeclarations := (additions.find? moduleName).getD {}
      additions := additions.insert moduleName (moduleDeclarations.insert name declaration)
  for (moduleName, added) in additions do
    let mut declarations ← unsafe loadPPModule moduleName
    for (name, declaration) in added do
      declarations := declarations.insert name declaration
    unsafe savePPModule moduleName declarations

unsafe def markFullyPP (roots : Array Name) : IO Unit := do
  let (path, depHash, root) ← unsafe ppRootData roots (toString ppVersion)
  pickle path (depHash, true) (Name.str root "_leanreachPPRoot")

end LeanReach.Cache
