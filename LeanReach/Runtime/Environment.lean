import Lean.Environment
import LeanReach.Runtime.Project
import Lake.Load.Manifest

namespace LeanReach

open Lean

private def workspaceRoots : IO (Array System.FilePath) := do
  let cwd ← (← Project.findDir?).getDM IO.currentDir
  let packages := cwd / ".lake" / "packages"
  let manifest ←
    try Lake.Manifest.load? (cwd / Lake.defaultManifestFile)
    catch _ => pure none
  let mut roots := #[cwd]
  if ← packages.isDir then
    for entry in ← packages.readDir do
      if ← entry.path.isDir then
        let root := if let some package := manifest >>= fun manifest =>
            manifest.packages.find? (Lake.PackageEntry.dirName · == entry.fileName) then
          match package.src with
          | .git (subDir? := some subDir) .. => entry.path / subDir
          | _ => entry.path
        else entry.path
        roots := roots.push root
  return roots

private def leanSysroot : IO System.FilePath := do
  if let some root ← IO.getEnv "LEAN_SYSROOT" then
    return root
  let hint := (← IO.appDir) / "leanreach.sysroot"
  if ← hint.pathExists then
    let root := System.FilePath.mk (← IO.FS.readFile hint).trimAscii.copy
    if ← (root / "lib" / "lean").isDir then
      return root
  findSysroot

private def initializeSearchPath (sysroot : System.FilePath)
    (roots : Array System.FilePath) : IO Unit := do
  let mut paths := #[]
  for root in roots do
    let path := root / ".lake" / "build" / "lib" / "lean"
    if ← path.isDir then paths := paths.push path
  initSearchPath sysroot paths.toList

private def sourceSearchPath (sysroot : System.FilePath)
    (roots : Array System.FilePath) : IO SearchPath := do
  let mut paths := #[]
  for root in roots do
    paths := paths.push root
    let source := root / "src"
    if ← source.isDir then paths := paths.push source
  if let some path ← IO.getEnv "LEAN_SRC_PATH" then
    paths := paths ++ (System.SearchPath.parse path).toArray
  return (paths.push (sysroot / "src" / "lean")).toList

unsafe def prepareSearchPath : IO Unit := do
  let roots ← workspaceRoots
  let sysroot ← leanSysroot
  initializeSearchPath sysroot roots

unsafe def prepareEnvironment : IO SearchPath := do
  let roots ← workspaceRoots
  let sysroot ← leanSysroot
  initializeSearchPath sysroot roots
  sourceSearchPath sysroot roots

unsafe def runCore {α : Type} (env : Environment) (action : CoreM α) : IO α :=
  Core.CoreM.toIO'
    action
    { fileName := "<leanreach>", fileMap := default }
    { env }

unsafe def importEnvironment (modules : Array Name) (leakEnv := false) : IO Environment := do
  Lean.enableInitializersExecution
  let imports := modules.map fun module => { module }
  importModules (loadExts := true) (leakEnv := leakEnv) imports {}

unsafe def detectRoots (refresh := false) : IO (Array Name) := do
  let roots ← unsafe Project.detectRoots (← leanSysroot) refresh
  if roots.isEmpty then
    throw <| IO.userError "could not detect a built local lean_lib or required Mathlib; use --module"
  return roots

end LeanReach
