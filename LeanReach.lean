import Lean.Util.Path
import LeanReach.Cache
import LeanReach.Query

namespace LeanReach

open Lean

private def workspaceRoots : IO (List System.FilePath) := do
  let cwd ← IO.currentDir
  let packages := cwd / ".lake" / "packages"
  let mut roots := [cwd]
  if ← packages.isDir then
    for entry in ← packages.readDir do
      if ← entry.path.isDir then roots := roots.concat entry.path
  return roots

private def initializeSearchPath (roots : List System.FilePath) : IO Unit := do
  match ← IO.getEnv "LEAN_PATH" with
  | some path => searchPathRef.set (System.SearchPath.parse path)
  | none =>
    let mut paths := []
    for root in roots do
      let path := root / ".lake" / "build" / "lib" / "lean"
      if ← path.isDir then paths := paths.concat path
    initSearchPath (← findSysroot) paths

private def sourceSearchPath (roots : List System.FilePath) : IO SearchPath := do
  let mut fallback := []
  for root in roots do
    fallback := fallback.concat root
    let source := root / "src"
    if ← source.isDir then fallback := fallback.concat source
  fallback := fallback.concat ((← findSysroot) / "src" / "lean")
  match ← IO.getEnv "LEAN_SRC_PATH" with
  | some path => return System.SearchPath.parse path ++ fallback
  | none => return fallback

private unsafe def withIndexSession {α : Type} (root : Name)
    (select : Index → Except String (Array Name)) (action : Session → CoreM α) : IO α := do
  let roots ← workspaceRoots
  initializeSearchPath roots
  let sourcePath ← sourceSearchPath roots
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
