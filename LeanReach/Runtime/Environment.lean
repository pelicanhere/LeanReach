import Lean.Util.Path
import LeanReach.Runtime.Project

namespace LeanReach

open Lean

private def workspaceRoots : IO (List System.FilePath) := do
  let cwd ← (← Project.findDir?).getDM IO.currentDir
  let packages := cwd / ".lake" / "packages"
  let mut roots := [cwd]
  if ← packages.isDir then
    for entry in ← packages.readDir do
      if ← entry.path.isDir then roots := roots.concat entry.path
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
    (roots : List System.FilePath) : IO Unit := do
  match ← IO.getEnv "LEAN_PATH" with
  | some path => searchPathRef.set (System.SearchPath.parse path)
  | none =>
    let mut paths := []
    for root in roots do
      let path := root / ".lake" / "build" / "lib" / "lean"
      if ← path.isDir then paths := paths.concat path
    initSearchPath sysroot paths

private def sourceSearchPath (sysroot : System.FilePath)
    (roots : List System.FilePath) : IO SearchPath := do
  let mut fallback := []
  for root in roots do
    fallback := fallback.concat root
    let source := root / "src"
    if ← source.isDir then fallback := fallback.concat source
  fallback := fallback.concat (sysroot / "src" / "lean")
  match ← IO.getEnv "LEAN_SRC_PATH" with
  | some path => return System.SearchPath.parse path ++ fallback
  | none => return fallback

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

unsafe def importEnvironment (modules : Array Name) (leakEnv := false)
    (level := OLeanLevel.exported) : IO Environment := do
  Lean.enableInitializersExecution
  let imports := modules.map fun module => { module }
  if level == .private then
    importModules (loadExts := true) (level := level) (leakEnv := leakEnv) imports {}
  else try
    importModules (loadExts := true) (level := level) (leakEnv := leakEnv) imports {}
  catch _ =>
    Lean.enableInitializersExecution
    importModules (loadExts := true) (leakEnv := leakEnv) imports {}

unsafe def detectRoots (refresh := false) : IO (Array Name) := do
  let roots ← unsafe Project.detectRoots (← leanSysroot) refresh
  if roots.isEmpty then
    throw <| IO.userError "could not detect a built local lean_lib or required Mathlib; use --module"
  return roots

end LeanReach
