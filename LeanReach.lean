import Lean.Util.Path
import LeanReach.Cache
import LeanReach.Query

namespace LeanReach

open Lean

private def initializeSearchPath : IO Unit := do
  match ← IO.getEnv "LEAN_PATH" with
  | some path => searchPathRef.set (System.SearchPath.parse path)
  | none => initSearchPath (← findSysroot)

private def sourceSearchPath : IO SearchPath := do
  let fallback := [← IO.currentDir, (← findSysroot) / "src" / "lean"]
  match ← IO.getEnv "LEAN_SRC_PATH" with
  | some path => return System.SearchPath.parse path ++ fallback
  | none => return fallback

private unsafe def withIndexSession {α : Type} (root : Name)
    (select : Index → Except String (Array Name)) (action : Session → CoreM α) : IO α := do
  initializeSearchPath
  let sourcePath ← sourceSearchPath
  Lean.enableInitializersExecution
  let index ← unsafe Cache.loadIndex root
  let modules ←
    match select index with
    | .ok modules => pure modules
    | .error message => throw <| IO.userError message
  let imports := modules.map fun moduleName => { module := moduleName }
  let env ←
    if imports.isEmpty then mkEmptyEnvironment
    else importModules (loadExts := true) imports {}
  Core.CoreM.toIO'
    (do action (← Session.create index sourcePath))
    { fileName := "<leanreach>", fileMap := default }
    { env }

/-- Import only the modules needed to render the selected declarations. -/
unsafe def withSessionFor {α : Type} (root : Name) (select : Index → Except String (Array Name))
    (action : Session → CoreM α) : IO α :=
  withIndexSession root (fun index => index.modulesFor <$> select index) action

/-- Import a root module once and reuse its environment and index for the entire action. -/
unsafe def withSession {α : Type} (root : Name) (action : Session → CoreM α) : IO α :=
  withIndexSession root (fun _ => pure #[root]) action

end LeanReach
