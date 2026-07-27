import Lean.Environment
import Lean.Server.References
import Lean.Util.Path
import LeanReach.BlackListed
import LeanReach.Index

namespace LeanReach.Cache

open Lean

private def version := 7
private def fragmentVersion := 2

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

private def depHash? (olean : System.FilePath) : IO (Option String) := do
  let path := olean.withExtension "trace"
  unless ← path.pathExists do return none
  return (Json.parse (← IO.FS.readFile path) >>= (·.getObjValAs? String "depHash")).toOption

private def sourceNames (olean : System.FilePath) : IO (Std.HashSet String) := do
  let path := olean.withExtension "ilean"
  unless ← path.pathExists do return {}
  let ilean ← Server.Ilean.load path
  let mut names := ilean.decls.foldl (init := {}) fun names name _ => names.insert name
  for (ident, info) in ilean.references do
    if info.definition?.isSome then
      if let .const _ name := ident then names := names.insert name
  return names

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
  return ({
    imports := data.imports.map (·.module)
    declarations := data.constants.filterMap fun info =>
      let name := info.name
      if source.contains name.toString && !isBlackListed name then
        some (name, info.getUsedConstantsAsSet)
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
    if ← path.pathExists then
      try
        let ((storedHash, fragment), _) ← unsafe unpickle (String × ModuleFragment) path
        if storedHash == hash then return fragment
      catch _ => pure ()
  if let some hash := hash? then
    try
      writeFragment moduleName olean path hash
      let ((_, fragment), _) ← unsafe unpickle (String × ModuleFragment) path
      return fragment
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

unsafe def loadIndex (root : Name) : IO Index := do
  let olean ← findOLean root
  let some depHash ← depHash? olean | return ← buildIndex root
  let path := olean.withExtension s!"leanreach-{version}"
  if ← path.pathExists then
    try
      let ((storedHash, index), _) ← unsafe unpickle (String × Index) path
      if storedHash == depHash then return index
    catch _ => pure ()
  let index ← buildIndex root
  try pickle path root (depHash, index)
  catch _ => IO.eprintln s!"leanreach: could not write cache {path}"
  return index

end LeanReach.Cache
