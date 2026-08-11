import Lake.Build.Common
import Lean.Environment

namespace LeanReach.Cache

open Lean

private initialize nextTempId : IO.Ref Nat ← IO.mkRef 0

def removeFileIfExists (path : System.FilePath) : IO Unit := do
  try IO.FS.removeFile path catch _ => pure ()

private def writeAtomically (path : System.FilePath)
    (write : System.FilePath → IO Unit) : IO Unit := do
  let pid ← IO.Process.getPID
  let id ← nextTempId.modifyGet fun id => (id, id + 1)
  let temp := System.FilePath.mk s!"{path}.tmp-{pid}-{id}"
  try
    write temp
    IO.FS.rename temp path
  finally removeFileIfExists temp

/-- Save a compacted Lean object with its dependency hash. Adapted from Loogle's `Pickle` module. -/
def savePart {α : Type} (path : System.FilePath) (depHash : String)
    (value : α) (key : Name) : IO Unit :=
  writeAtomically path fun temp =>
    saveModuleData temp key (unsafe unsafeCast (depHash, value))

def saveBytes (path : System.FilePath) (value : ByteArray) : IO Unit :=
  writeAtomically path fun temp => IO.FS.writeBinFile temp value

def saveShards (count : Nat) (save : Nat → IO Unit)
    (progress : Nat → Nat → IO Unit := fun _ _ => pure ()) : IO Unit := do
  progress 0 count
  let mut offset := 0
  while offset < count do
    let stop := min count (offset + 16)
    let tasks ← (Array.range (stop - offset)).mapM fun delta =>
      IO.asTask (save (offset + delta))
    tasks.forM fun task => IO.ofExcept task.get
    offset := stop
    progress offset count

def loadedKey (path : System.FilePath) (depHash : String) : String :=
  s!"{path}\u0000{depHash}"

unsafe def loadPart (α : Type) (path : System.FilePath) (depHash : String) :
    IO (Option α) := do
  unless ← path.pathExists do return none
  try
    let (raw, region) ← readModuleData path
    try
      let (storedHash, value) : String × α := unsafeCast raw
      if storedHash == depHash then return some value
    catch _ => pure ()
    region.free
  catch _ => pure ()
  return none

def markerMatches (path : System.FilePath) (value : String) : IO Bool := do
  unless ← path.pathExists do return false
  try return (← IO.FS.readFile path) == value
  catch _ => return false

private def oleanParts (olean : System.FilePath) : Array System.FilePath :=
  #[OLeanLevel.exported, OLeanLevel.server, OLeanLevel.private].map
    (·.adjustFileName olean)

private def buildMetadata? (olean : System.FilePath) : IO (Option Lake.BuildMetadata) := do
  try
    let result := Lake.BuildMetadata.parse
      (← IO.FS.readFile (olean.withExtension "trace"))
    return result.toOption
  catch _ => return none

private def partHash? (olean : System.FilePath) : IO (Option String) := do
  let hashes ← (← (oleanParts olean).filterM (·.pathExists)).mapM fun path =>
    toString <$> Lake.computeFileHash path
  return if hashes.isEmpty then none else some (String.intercalate ":" hashes.toList)

def depHash? (olean : System.FilePath) : IO (Option String) := do
  if let some metadata ← buildMetadata? olean then
    return some (toString metadata.depHash)
  partHash? olean

/-- Hashes only the emitted `.olean` layers, excluding transitive build inputs. -/
def oleanHash? (olean : System.FilePath) : IO (Option String) := do
  if let some outputs := (← buildMetadata? olean).bind (·.outputs?) then
    let hashes : Except String (Array String) := outputs.getObjValAs? (Array String) "o"
    if let .ok hashes := hashes then
      if !hashes.isEmpty then return some (String.intercalate ":" hashes.toList)
  partHash? olean

private def rootStamp (olean : System.FilePath) : IO String := do
  let trace := olean.withExtension "trace"
  let paths ←
    if ← trace.pathExists then pure #[trace]
    else (oleanParts olean).filterM (·.pathExists)
  let stamps ← paths.mapM fun path => do
    let metadata ← path.metadata
    return s!"{path}:{metadata.modified.sec}:{metadata.modified.nsec}:{metadata.byteSize}"
  return String.intercalate "|" stamps.toList

private abbrev RootInfo := System.FilePath × String × Name

private initialize rootInfoCache : IO.Ref (Std.HashMap String RootInfo) ← IO.mkRef {}

unsafe def rootData (roots : Array Name) : IO (System.FilePath × String × Name) := do
  let some root := roots[0]? | throw <| IO.userError "no root modules"
  let key := String.intercalate "\u0000" (roots.toList.map toString)
  if let some info := (← rootInfoCache.get).get? key then return info
  let oleans ← roots.mapM findOLean
  let olean := oleans[0]!
  let stamps ← oleans.mapM rootStamp
  let stamp := String.intercalate "\u0001" <| (roots.zip stamps).toList.map fun (name, value) =>
    s!"{name}\t{value}"
  -- Root-hash cache format 1.
  let cache := olean.withExtension "leanreach-root-hash-1"
  if ← cache.pathExists then
    try
      let storedStamp :: depHash :: _ := (← IO.FS.readFile cache).splitOn "\n" | pure ()
      if storedStamp == stamp then
        let info := (olean, depHash, root)
        rootInfoCache.modify (·.insert key info)
        return info
    catch _ => pure ()
  let hashes ← (roots.zip oleans).mapM fun (name, path) => do
    let some hash ← depHash? path |
      throw <| IO.userError s!"could not hash root module '{name}'"
    return s!"{name}:{hash}"
  let depHash := String.intercalate ":" hashes.toList
  try IO.FS.writeFile cache (stamp ++ "\n" ++ depHash)
  catch _ => pure ()
  let info := (olean, depHash, root)
  rootInfoCache.modify (·.insert key info)
  return info

end LeanReach.Cache
