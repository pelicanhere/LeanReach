import Lean.Environment
import LeanReach.Runtime.Project

namespace LeanReach

open Lean

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
    (layout? : Option Project.Layout) : IO Unit :=
  initSearchPath sysroot (layout?.map (·.leanPath.toList) |>.getD [])

private def sourceSearchPath (sysroot : System.FilePath)
    (layout? : Option Project.Layout) : IO SearchPath := do
  let mut paths := layout?.map (·.sourcePath) |>.getD #[]
  if let some path ← IO.getEnv "LEAN_SRC_PATH" then
    paths := paths ++ (System.SearchPath.parse path).toArray
  return (paths.push (sysroot / "src" / "lean")).toList

private unsafe def prepareLayout : IO (System.FilePath × Option Project.Layout) := do
  let sysroot ← leanSysroot
  let layout? ← unsafe Project.loadLayout? sysroot
  initializeSearchPath sysroot layout?
  return (sysroot, layout?)

unsafe def prepareSearchPath : IO Unit := do
  discard <| unsafe prepareLayout

unsafe def prepareEnvironment : IO SearchPath := do
  let (sysroot, layout?) ← unsafe prepareLayout
  sourceSearchPath sysroot layout?

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
  let some layout ← unsafe Project.loadLayout? (← leanSysroot) refresh |
    throw <| IO.userError "could not detect a built local lean_lib or required Mathlib; use --module"
  if layout.roots.isEmpty then
    throw <| IO.userError "could not detect a built local lean_lib or required Mathlib; use --module"
  return layout.roots

end LeanReach
