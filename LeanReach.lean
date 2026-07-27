import Lean.Util.Path
import LeanReach.Query

namespace LeanReach

open Lean

private def initializePaths : IO SearchPath := do
  match ← IO.getEnv "LEAN_PATH" with
  | some path => searchPathRef.set (System.SearchPath.parse path)
  | none => initSearchPath (← findSysroot)
  let fallback := [← IO.currentDir, (← findSysroot) / "src" / "lean"]
  match ← IO.getEnv "LEAN_SRC_PATH" with
  | some path => return System.SearchPath.parse path ++ fallback
  | none => return fallback

/-- Import a root module once and reuse its environment and index for the entire action. -/
unsafe def withSession {α : Type} (root : Name) (action : Session → CoreM α) : IO α := do
  let sourcePath ← initializePaths
  Lean.enableInitializersExecution
  let env ← importModules (loadExts := true) #[{ module := root }] {}
  Core.CoreM.toIO'
    (do action (← Session.create (← unsafe Index.load root) sourcePath))
    { fileName := "<leanreach>", fileMap := default }
    { env }

end LeanReach
