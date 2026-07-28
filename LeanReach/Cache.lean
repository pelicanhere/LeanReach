import Batteries.Util.Pickle
import Lake.Build.Trace
import Lean.Server.References
import Lean.Util.Path
import LeanReach.BlackListed
import LeanReach.Declaration
import LeanReach.Index

namespace LeanReach.Cache

open Lean

private def catalogVersion := 1
private def relationsVersion := 2
private def fragmentVersion := 3
private def renderVersion := 2

structure ModuleFragment where
  imports : Array Name
  declarations : Array (Name × NameSet)

/-- Save a compacted Lean object. Adapted from Loogle's `Pickle` module. -/
private unsafe def loadPart (α : Type) (path : System.FilePath) (depHash : String) :
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

private def sourceNames (olean : System.FilePath) : IO (Std.HashSet String) := do
  let path := olean.withExtension "ilean"
  unless ← path.pathExists do return {}
  let ilean ← Server.Ilean.load path
  let mut names := ilean.decls.foldl (init := {}) fun names name _ => names.insert name
  for (ident, info) in ilean.references do
    if info.definition?.isSome then
      if let .const _ name := ident then names := names.insert name
  return names

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
  let mut paths := #[olean]
  for level in #[OLeanLevel.server, OLeanLevel.private] do
    let path := level.adjustFileName olean
    if ← path.pathExists then paths := paths.push path
  let parts ← readModuleDataParts paths
  let some (data, _) := parts.back? |
    throw <| IO.userError s!"empty module data for '{moduleName}'"
  let source ← sourceNames olean
  let internal := data.constants.foldl (init := ({} : NameMap NameSet)) fun internal info =>
    if isBlackListed info.name then
      internal.insert info.name info.getUsedConstantsAsSet
    else internal
  return ({
    imports := data.imports.map (·.module)
    declarations := data.constants.filterMap fun info =>
      let name := info.name
      if source.contains name.toString && !isBlackListed name then
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

private unsafe def rootData (roots : Array Name) : IO (System.FilePath × String × Name) := do
  let some root := roots[0]? | throw <| IO.userError "no root modules"
  let olean ← findOLean root
  let some firstHash ← depHash? olean |
    throw <| IO.userError s!"could not hash root module '{root}'"
  if roots.size == 1 then return (olean, firstHash, root)
  let mut hashes := #[s!"{root}:{firstHash}"]
  for root in roots.extract 1 roots.size do
    let some hash ← depHash? (← findOLean root) |
      throw <| IO.userError s!"could not hash root module '{root}'"
    hashes := hashes.push s!"{root}:{hash}"
  return (olean, String.intercalate ":" hashes.toList, root)

unsafe def loadIndex (roots : Array Name) (loadRelations := true) : IO Index := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "leanreach" else "leanreach-roots"
  let catalogPath := olean.withExtension s!"{stem}-catalog-{catalogVersion}"
  let relationsPath := olean.withExtension s!"{stem}-relations-{relationsVersion}"
  if let some catalog ← unsafe loadPart Catalog catalogPath depHash then
    if !loadRelations then return Index.ofParts catalog (#[], #[])
    if let some relations ← unsafe loadPart Relations relationsPath depHash then
      return Index.ofParts catalog relations
  let index ← buildIndex roots
  try
    pickle catalogPath (depHash, index.catalog) (Name.str root "_leanreachCatalog")
    pickle relationsPath (depHash, index.relations) (Name.str root "_leanreachRelations")
  catch _ => IO.eprintln "leanreach: could not write root index cache"
  if loadRelations then return index
  return Index.ofParts index.catalog (#[], #[])

unsafe def loadRenderedModule (moduleName : Name) : IO (NameMap Declaration) := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return {}
  let path := olean.withExtension s!"leanreach-render-{renderVersion}"
  return (← unsafe loadPart (NameMap Declaration) path depHash).getD {}

unsafe def isFullyRendered (roots : Array Name) : IO Bool := do
  let (olean, depHash, _) ← unsafe rootData roots
  let stem := if roots.size == 1 then "root" else "roots"
  let path := olean.withExtension s!"leanreach-render-{stem}-{renderVersion}"
  return (← unsafe loadPart Bool path depHash).getD false

unsafe def loadRenderProgress (roots : Array Name) : IO NameSet := do
  let (olean, depHash, _) ← unsafe rootData roots
  let stem := if roots.size == 1 then "root" else "roots"
  let path := olean.withExtension s!"leanreach-render-{stem}-progress-{renderVersion}"
  return (← unsafe loadPart NameSet path depHash).getD {}

unsafe def saveRenderProgress (roots : Array Name) (modules : NameSet) : IO Unit := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "root" else "roots"
  let path := olean.withExtension s!"leanreach-render-{stem}-progress-{renderVersion}"
  pickle path (depHash, modules) (Name.str root "_leanreachRenderProgress")

unsafe def loadRendered (index : Index) (names : Array Name) : IO (NameMap Declaration) := do
  let mut byModule : NameMap (Array Name) := {}
  for name in names do
    if let some moduleName := index.moduleOf? name then
      byModule := byModule.insert moduleName
        ((byModule.find? moduleName).getD #[] |>.push name)
  let mut declarations := {}
  for (moduleName, names) in byModule do
    let cached ← unsafe loadRenderedModule moduleName
    for name in names do
      if let some declaration := cached.find? name then
        declarations := declarations.insert name declaration
  return declarations

unsafe def saveRenderedModule (moduleName : Name) (declarations : NameMap Declaration) :
    IO Unit := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return
  let path := olean.withExtension s!"leanreach-render-{renderVersion}"
  pickle path (depHash, declarations) (Name.str moduleName "_leanreachRender")

unsafe def saveRendered (before after : NameMap Declaration) : IO Unit := do
  let mut additions : NameMap (NameMap Declaration) := {}
  for (name, declaration) in after do
    unless before.contains name do
      let moduleName := declaration.moduleName.toName
      let moduleDeclarations := (additions.find? moduleName).getD {}
      additions := additions.insert moduleName (moduleDeclarations.insert name declaration)
  for (moduleName, added) in additions do
    let mut declarations ← unsafe loadRenderedModule moduleName
    for (name, declaration) in added do
      declarations := declarations.insert name declaration
    unsafe saveRenderedModule moduleName declarations

unsafe def markFullyRendered (roots : Array Name) : IO Unit := do
  let (olean, depHash, root) ← unsafe rootData roots
  let stem := if roots.size == 1 then "root" else "roots"
  let path := olean.withExtension s!"leanreach-render-{stem}-{renderVersion}"
  pickle path (depHash, true) (Name.str root "_leanreachRenderRoot")

end LeanReach.Cache
