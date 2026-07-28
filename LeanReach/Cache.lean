import Lake.Build.Trace
import Lean.Environment
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
private def pickle {α : Type} (path : System.FilePath) (key : Name) (value : α) : IO Unit :=
  saveModuleData path key (unsafe unsafeCast value)

/-- Load a compacted Lean object and its region handle. -/
private unsafe def unpickle (α : Type) (path : System.FilePath) : IO (α × CompactedRegion) := do
  let (value, region) ← readModuleData path
  return (unsafeCast value, region)

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
    pickle path moduleName (hash, fragment)
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

private unsafe def buildIndex (root : Name) : IO Index := do
  let mut pending := #[root]
  let mut seen : NameHashSet := {}
  let mut declarations := #[]
  while let some moduleName := pending.back? do
    pending := pending.pop
    unless seen.contains moduleName do
      seen := seen.insert moduleName
      let fragment ← loadFragment moduleName
      pending := pending ++ fragment.imports
      for (name, dependencies) in fragment.declarations do
        declarations := declarations.push (name, moduleName, dependencies)
  return Index.build declarations

unsafe def loadIndex (root : Name) (loadRelations := true) : IO Index := do
  let olean ← findOLean root
  let some depHash ← depHash? olean | return ← buildIndex root
  let catalogPath := olean.withExtension s!"leanreach-catalog-{catalogVersion}"
  let relationsPath := olean.withExtension s!"leanreach-relations-{relationsVersion}"
  if let some catalog ← unsafe loadPart Catalog catalogPath depHash then
    if !loadRelations then return Index.ofParts catalog (#[], #[])
    if let some relations ← unsafe loadPart Relations relationsPath depHash then
      return Index.ofParts catalog relations
  let index ← buildIndex root
  try
    pickle catalogPath (Name.str root "_leanreachCatalog") (depHash, index.catalog)
    pickle relationsPath (Name.str root "_leanreachRelations") (depHash, index.relations)
  catch _ => IO.eprintln "leanreach: could not write root index cache"
  if loadRelations then return index
  return Index.ofParts index.catalog (#[], #[])

private unsafe def loadRenderedModule (moduleName : Name) : IO (NameMap Declaration) := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return {}
  let path := olean.withExtension s!"leanreach-render-{renderVersion}"
  return (← unsafe loadPart (NameMap Declaration) path depHash).getD {}

unsafe def isFullyRendered (root : Name) : IO Bool := do
  let olean ← findOLean root
  let some depHash ← depHash? olean | return false
  let path := olean.withExtension s!"leanreach-render-root-{renderVersion}"
  return (← unsafe loadPart Bool path depHash).getD false

unsafe def loadRendered (modules : Array Name) : IO (NameMap Declaration) := do
  let mut declarations := {}
  for moduleName in modules do
    for (name, declaration) in ← unsafe loadRenderedModule moduleName do
      declarations := declarations.insert name declaration
  return declarations

unsafe def saveRenderedModule (moduleName : Name) (declarations : NameMap Declaration) :
    IO Unit := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return
  let path := olean.withExtension s!"leanreach-render-{renderVersion}"
  pickle path (Name.str moduleName "_leanreachRender") (depHash, declarations)

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

unsafe def markFullyRendered (root : Name) : IO Unit := do
  let olean ← findOLean root
  let some depHash ← depHash? olean | return
  let path := olean.withExtension s!"leanreach-render-root-{renderVersion}"
  pickle path (Name.str root "_leanreachRenderRoot") (depHash, true)

end LeanReach.Cache
