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

private unsafe def prepareEnvironment : IO SearchPath := do
  let roots ← workspaceRoots
  let sysroot ← leanSysroot
  initializeSearchPath sysroot roots
  Lean.enableInitializersExecution
  sourceSearchPath sysroot roots

private unsafe def withIndexSession {α : Type} (root : Name)
    (loadRelations : Bool)
    (select : Index → Except String (Array Name))
    (forceRootImport : Bool)
    (action : Session → CoreM α) : IO α := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex root loadRelations
  let names ←
    match select index with
    | .ok names => pure names
    | .error message => throw <| IO.userError message
  let rendered ← unsafe Cache.loadRendered (index.modulesFor names)
  let modules :=
    if forceRootImport then #[root]
    else index.modulesFor (names.filter fun name => !rendered.contains name)
  let imports := modules.map fun moduleName => { module := moduleName }
  let env ←
    if imports.isEmpty then mkEmptyEnvironment
    else importModules (loadExts := true) imports {}
  let session ← Session.create index sourcePath rendered
  let result ← Core.CoreM.toIO'
    (action session)
    { fileName := "<leanreach>", fileMap := default }
    { env }
  let updated ← session.rendered
  if updated.size != rendered.size then
    try unsafe Cache.saveRendered rendered updated
    catch _ => IO.eprintln "leanreach: could not write rendered declaration cache"
  return result

/-- Import only the modules needed to render the selected declarations. -/
unsafe def withSessionFor {α : Type} (root : Name) (select : Index → Except String (Array Name))
    (loadRelations : Bool) (action : Session → CoreM α) : IO α :=
  withIndexSession root loadRelations select false action

/-- Import a root module once and reuse its environment and index for the entire action. -/
unsafe def withSession {α : Type} (root : Name) (action : Session → CoreM α) : IO α :=
  withIndexSession root true (fun _ => pure #[]) true action

/-- Pre-render every declaration below a root, checkpointing once per defining module. -/
unsafe def cacheRoot (root : Name)
    (progress : Name → Nat → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  let sourcePath ← prepareEnvironment
  if ← unsafe Cache.isFullyRendered root then return 0
  let index ← unsafe Cache.loadIndex root false
  let mut pending := #[]
  for (moduleName, names) in index.declarationsByModule do
    let rendered ← unsafe Cache.loadRendered #[moduleName]
    if names.any fun name => !rendered.contains name then
      pending := pending.push (moduleName, names)
  if pending.isEmpty then
    unsafe Cache.markFullyRendered root
    return 0
  let mut count := 0
  for start in [0:pending.size:128] do
    let batch := pending.extract start (min pending.size (start + 128))
    let env ← importModules (batch.map fun (moduleName, _) => { module := moduleName }) {}
    for ((moduleName, names), offset) in batch.zipIdx do
      let before ← unsafe Cache.loadRendered #[moduleName]
      let render := fun (env : Environment) => do
        let session ← Session.create index sourcePath before
        Core.CoreM.toIO'
          (discard <| session.cacheNames names)
          { fileName := "<leanreach-cache>", fileMap := default }
          { env }
        session.rendered
      let after ←
        try render env
        catch _ => render (← importModules #[{ module := moduleName }] {})
      count := count + after.size - before.size
      unsafe Cache.saveRenderedModule moduleName after
      progress moduleName (start + offset + 1) pending.size
  unsafe Cache.markFullyRendered root
  return count

end LeanReach
