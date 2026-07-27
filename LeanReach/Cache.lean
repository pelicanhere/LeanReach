import Lean.Environment
import Lean.Util.Path
import LeanReach.Index

namespace LeanReach.Cache

open Lean

private def version := 5

/-- Save a compacted Lean object. Adapted from Loogle's `Pickle` module. -/
private def pickle {α : Type} (path : System.FilePath) (value : α) : IO Unit :=
  saveModuleData path `LeanReach.cache (unsafe unsafeCast value)

/-- Load a compacted Lean object and its region handle. -/
private unsafe def unpickle (α : Type) (path : System.FilePath) : IO (α × CompactedRegion) := do
  let (value, region) ← readModuleData path
  return (unsafeCast value, region)

private def depHash? (root : Name) : IO (Option String) := do
  let path := (← findOLean root).withExtension "trace"
  unless ← path.pathExists do return none
  return (Json.parse (← IO.FS.readFile path) >>= (·.getObjValAs? String "depHash")).toOption

unsafe def loadIndex (root : Name) : CoreM Index := do
  let some depHash ← depHash? root | return ← Index.build
  let path := (← findOLean root).withExtension s!"leanreach-{version}"
  if ← path.pathExists then
    try
      let ((storedHash, index), _) ← unsafe unpickle (String × Index) path
      if storedHash == depHash then return index
    catch _ => pure ()
  let index ← Index.build
  try pickle path (depHash, index)
  catch _ => IO.eprintln s!"leanreach: could not write cache {path}"
  return index

end LeanReach.Cache
