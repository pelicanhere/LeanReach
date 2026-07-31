import LeanReach.Cache.Storage
import LeanReach.PrettyPrint.Declaration
import LeanReach.Search.Types

namespace LeanReach.Cache

open Lean

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
  -- Single-root marker format 8; multi-root marker format 9.
  let suffix := if roots.size == 1 then "root-8" else "roots-9"
  return (olean.withExtension s!"leanreach-pp-{suffix}", depHash)

unsafe def isFullyPP (roots : Array Name) : IO Bool := do
  let (path, depHash) ← unsafe ppRootData roots
  markerMatches path depHash

unsafe def loadPP (moduleOf? : Name → Option Name)
    (names : Array Name) : IO (NameMap Declaration) := do
  let mut declarations := {}
  for (moduleName, names) in groupNamesByModule moduleOf? names do
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

unsafe def markFullyPP (roots : Array Name) : IO Unit := do
  let (path, depHash) ← unsafe ppRootData roots
  IO.FS.writeFile path depHash

end LeanReach.Cache
