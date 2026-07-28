import Lean.Util.Path
import LeanReach.Cache
import LeanReach.Project
import LeanReach.Query

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

private unsafe def prepareEnvironment : IO SearchPath := do
  let roots ← workspaceRoots
  let sysroot ← leanSysroot
  initializeSearchPath sysroot roots
  sourceSearchPath sysroot roots

private def selectNames (index : Index) (select : Index → Except String (Array Name)) :
    IO (Array Name) :=
  match select index with
  | .ok names => pure names
  | .error message => throw <| IO.userError message

private unsafe def runSession {α : Type} (index : Index) (session : Session)
    (names : Array Name) (modules? : Option (Array Name)) (wholeModules : Bool)
    (action : CoreM α) : IO α := do
  let current ← session.rendered
  let missing := names.filter fun name => !current.contains name
  if wholeModules then
    for moduleName in index.modulesFor missing do
      session.merge (← unsafe Cache.loadRenderedModule moduleName)
  else
    session.merge (← unsafe Cache.loadRendered index missing)
  let before ← session.rendered
  let modules := modules?.getD <|
    index.modulesFor (names.filter fun name => !before.contains name)
  let env ←
    if modules.isEmpty then mkEmptyEnvironment
    else
      Lean.enableInitializersExecution
      importModules (loadExts := true) (modules.map fun moduleName => { module := moduleName }) {}
  let result ← Core.CoreM.toIO'
    action
    { fileName := "<leanreach>", fileMap := default }
    { env }
  let after ← session.rendered
  if after.size != before.size then
    try unsafe Cache.saveRendered before after
    catch _ => IO.eprintln "leanreach: could not write rendered declaration cache"
  return result

private unsafe def withIndexSession {α : Type} (roots : Array Name)
    (loadRelations : Bool)
    (select : Index → Except String (Array Name))
    (forceRootImport : Bool)
    (action : Session → CoreM α) : IO α := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex roots loadRelations
  let names ← selectNames index select
  let session ← Session.create index sourcePath
  unsafe runSession index session names (if forceRootImport then some roots else none) false
    (action session)

/-- Import only the modules needed to render the selected declarations. -/
unsafe def withSessionFor {α : Type} (roots : Array Name)
    (select : Index → Except String (Array Name)) (loadRelations : Bool)
    (action : Session → CoreM α) : IO α :=
  withIndexSession roots loadRelations select false action

/-- Import the root modules once and reuse their environment and index for the entire action. -/
unsafe def withSession {α : Type} (roots : Array Name) (action : Session → CoreM α) : IO α :=
  withIndexSession roots true (fun _ => pure #[]) true action

abbrev SessionRunner :=
  (Index → Except String (Array Name)) → (Array Name → CoreM Unit) → IO Unit

unsafe def withLazySession {α : Type} (roots : Array Name)
    (action : Session → SessionRunner → IO α) : IO α := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex roots true
  let session ← Session.create index sourcePath
  let run : SessionRunner := fun select query => do
    let names ← selectNames index select
    discard <| unsafe runSession index session names none true (query names)
  action session run

unsafe def detectRoots : IO (Array Name) := do
  let roots ← unsafe Project.detectRoots (← leanSysroot)
  if roots.isEmpty then
    throw <| IO.userError "could not detect a built local lean_lib or required Mathlib; use --module"
  return roots

/-- Pre-render every declaration below a root, checkpointing once per defining module. -/
unsafe def cacheRoots (roots : Array Name)
    (progress : Name → Nat → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  discard <| prepareEnvironment
  if ← unsafe Cache.isFullyRendered roots then return 0
  let index ← unsafe Cache.loadIndex roots false
  let mut completed ← unsafe Cache.loadRenderProgress roots
  let mut pending := #[]
  for (moduleName, names) in index.declarationsByModule do
    unless completed.contains moduleName do
      pending := pending.push (moduleName, names)
  if pending.isEmpty then
    unsafe Cache.markFullyRendered roots
    return 0
  let executable ← IO.appPath
  let mut count := 0
  for ((moduleName, names), done) in pending.zipIdx do
    let before ← unsafe Cache.loadRenderedModule moduleName
    unless names.all before.contains do
      let command := #["cache", moduleName.toString, "--json"]
      let args :=
        if roots.size == 1 then
          #["--module", roots[0]!.toString] ++ command
        else command
      let output ← IO.Process.output { cmd := executable.toString, args }
      unless output.exitCode == 0 do
        throw <| IO.userError s!"failed to cache '{moduleName}': {output.stderr.trimAscii.copy}"
      let after ← unsafe Cache.loadRenderedModule moduleName
      unless names.all after.contains do
        throw <| IO.userError s!"incomplete cache for '{moduleName}'"
      count := count + after.size - before.size
    completed := completed.insert moduleName
    unsafe Cache.saveRenderProgress roots completed
    progress moduleName (done + 1) pending.size
  unsafe Cache.markFullyRendered roots
  return count

end LeanReach
