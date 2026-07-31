import LeanReach.Cache.Storage
import LeanReach.PrettyPrint.Declaration

namespace LeanReach.Cache

open Lean

abbrev PPBatch := NameMap (NameMap Declaration)

private def ppPath (olean : System.FilePath) : System.FilePath :=
  -- Module PP cache format 3.
  olean.withExtension "leanreach-pp-3"

private abbrev PPStamp := IO.FS.SystemTime × UInt64
private abbrev CachedPP := Option PPStamp × NameMap Declaration

private initialize loadedPP : IO.Ref (Std.HashMap String CachedPP) ← IO.mkRef {}

private def ppStamp? (path : System.FilePath) : IO (Option PPStamp) := do
  unless ← path.pathExists do return none
  try
    let metadata ← path.metadata
    return some (metadata.modified, metadata.byteSize)
  catch _ => return none

unsafe def loadPPModule (moduleName : Name) : IO (NameMap Declaration) := do
  let olean ← findOLean moduleName
  let some depHash ← depHash? olean | return {}
  let path := ppPath olean
  let stamp ← ppStamp? path
  let key := loadedKey path depHash
  if let some (cachedStamp, declarations) := (← loadedPP.get).get? key then
    if cachedStamp == stamp then return declarations
  let declarations :=
    (← unsafe loadPart (NameMap Declaration) path depHash).getD {}
  loadedPP.modify (·.insert key (stamp, declarations))
  return declarations

private unsafe def ppRootData (roots : Array Name) :
    IO (System.FilePath × String) := do
  let (olean, depHash, _) ← unsafe rootData roots
  -- Single-root marker format 7; multi-root marker format 8.
  let suffix := if roots.size == 1 then "root-7" else "roots-8"
  return (olean.withExtension s!"leanreach-pp-{suffix}", depHash)

unsafe def isFullyPP (roots : Array Name) : IO Bool := do
  let (path, depHash) ← unsafe ppRootData roots
  if ← markerMatches path depHash then return true
  -- Accept object markers written by earlier versions.
  return (← unsafe loadPart Bool path depHash).getD false

unsafe def loadPP (moduleOf? : Name → Option Name)
    (names : Array Name) : IO (NameMap Declaration) := do
  let mut byModule : NameMap (Array Name) := {}
  for name in names do
    if let some moduleName := moduleOf? name then
      byModule := byModule.alter moduleName fun names =>
        some ((names.getD #[]).push name)
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
  let path := ppPath olean
  savePart path depHash declarations (Name.str moduleName "_leanreachPP")
  loadedPP.modify (·.erase (loadedKey path depHash))

unsafe def mergePPModule (moduleName : Name) (added : NameMap Declaration) :
    IO Unit := do
  let current ← unsafe loadPPModule moduleName
  unsafe savePPModule moduleName (current.insertMany added)

unsafe def savePP (additions : PPBatch) : IO Unit := do
  for (moduleName, added) in additions do
    unsafe mergePPModule moduleName added

unsafe def markFullyPP (roots : Array Name) : IO Unit := do
  let (path, depHash) ← unsafe ppRootData roots
  IO.FS.writeFile path depHash

end LeanReach.Cache
