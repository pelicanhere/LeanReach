import Lake.Build.Trace
import Lean.Environment
import Lean.Util.Path

namespace LeanReach.Cache

open Lean

private def rootHashVersion := 1

/-- Save a compacted Lean object. Adapted from Loogle's `Pickle` module. -/
def pickle {α : Type} (path : System.FilePath) (value : α) (key : Name) : IO Unit :=
  saveModuleData path key (unsafe unsafeCast value)

unsafe def loadPart (α : Type) (path : System.FilePath) (depHash : String) :
    IO (Option α) := do
  unless ← path.pathExists do return none
  try
    let (raw, _) ← readModuleData path
    let (storedHash, value) : String × α := unsafeCast raw
    if storedHash == depHash then return some value
  catch _ => pure ()
  return none

def markerMatches (path : System.FilePath) (value : String) : IO Bool := do
  unless ← path.pathExists do return false
  try return (← IO.FS.readFile path) == value
  catch _ => return false

def depHash? (olean : System.FilePath) : IO (Option String) := do
  let path := olean.withExtension "trace"
  if ← path.pathExists then
    return (Json.parse (← IO.FS.readFile path) >>= (·.getObjValAs? String "depHash")).toOption
  let mut hashes := #[]
  for level in #[OLeanLevel.exported, OLeanLevel.server, OLeanLevel.private] do
    let path := level.adjustFileName olean
    if ← path.pathExists then
      hashes := hashes.push (toString (← Lake.computeFileHash path))
  return if hashes.isEmpty then none else some (String.intercalate ":" hashes.toList)

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

end LeanReach.Cache
