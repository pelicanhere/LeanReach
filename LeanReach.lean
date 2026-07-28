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

private def selectPlan {α : Type} (index : Index)
    (select : Index → Except String (α × Array Name)) : IO (α × Array Name) :=
  match select index with
  | .ok plan => pure plan
  | .error message => throw <| IO.userError message

private unsafe def runSession {α : Type} (index : Index) (session : Session)
    (names : Array Name) (modules? : Option (Array Name)) (wholeModules : Bool)
    (emptyEnv? : Option Environment) (action : CoreM α) : IO α := do
  let missing ← session.missing names
  if wholeModules then
    for moduleName in index.modulesFor missing do
      session.merge (← unsafe Cache.loadPPModule moduleName)
  else
    session.merge (← unsafe Cache.loadPP index missing)
  let before ← session.ppCache
  let modules := modules?.getD <|
    index.modulesFor (← session.missing names)
  let env ←
    if modules.isEmpty then emptyEnv?.getDM mkEmptyEnvironment
    else
      Lean.enableInitializersExecution
      importModules (loadExts := true) (modules.map fun moduleName => { module := moduleName }) {}
  let result ← Core.CoreM.toIO'
    action
    { fileName := "<leanreach>", fileMap := default }
    { env }
  let after ← session.ppCache
  if after.size != before.size then
    try unsafe Cache.savePP before after
    catch _ => IO.eprintln "leanreach: could not write pretty-print cache"
  return result

private unsafe def withIndexSession {α β : Type} (roots : Array Name)
    (loadRelations : Bool)
    (select : Index → Except String (α × Array Name))
    (forceRootImport : Bool)
    (action : Session → α → CoreM β) : IO β := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex roots loadRelations
  let (plan, names) ← selectPlan index select
  let session ← Session.create index sourcePath (← unsafe Cache.loadPPBundle roots index)
  unsafe runSession index session names (if forceRootImport then some roots else none) false none
    (action session plan)

/-- Import only the modules needed to pretty-print the selected declarations. -/
unsafe def withSessionFor {α β : Type} (roots : Array Name)
    (select : Index → Except String (α × Array Name)) (loadRelations : Bool)
    (action : Session → α → CoreM β) : IO β :=
  withIndexSession roots loadRelations select false action

/-- Import the root modules once and reuse their environment and index for the entire action. -/
unsafe def withSession {α : Type} (roots : Array Name) (action : Session → CoreM α) : IO α :=
  withIndexSession roots true (fun _ => pure ((), #[])) true fun session _ => action session

abbrev SessionRunner :=
  {α : Type} → (Index → Except String (α × Array Name)) → (α → CoreM Unit) → IO Unit

unsafe def withLazySession {α : Type} (roots : Array Name)
    (action : Session → SessionRunner → IO α) : IO α := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex roots true
  let session ← Session.create index sourcePath (← unsafe Cache.loadPPBundle roots index)
  let emptyEnv ← mkEmptyEnvironment
  let run : SessionRunner := fun select query => do
    let (plan, names) ← selectPlan index select
    discard <| unsafe runSession index session names none true (some emptyEnv) (query plan)
  action session run

unsafe def detectRoots : IO (Array Name) := do
  let roots ← unsafe Project.detectRoots (← leanSysroot)
  if roots.isEmpty then
    throw <| IO.userError "could not detect a built local lean_lib or required Mathlib; use --module"
  return roots

/-- Pretty-print every declaration below a root, checkpointing once per defining module. -/
unsafe def cacheRoots (roots : Array Name)
    (progress : Name → Nat → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  discard <| prepareEnvironment
  let index ← unsafe Cache.loadIndex roots false
  if ← unsafe Cache.isFullyPP roots then
    if (← unsafe Cache.loadPPBundle roots index).isEmpty then
      unsafe Cache.savePPBundle roots index
    return 0
  let mut completed ← unsafe Cache.loadPPProgress roots
  let mut pending := #[]
  for (moduleName, names) in index.declarationsByModule do
    unless completed.contains moduleName do
      pending := pending.push (moduleName, names)
  let mut count := 0
  unless pending.isEmpty do
    let executable ← IO.appPath
    for ((moduleName, names), done) in pending.zipIdx do
      let before ← unsafe Cache.loadPPModule moduleName
      unless names.all before.contains do
        let command := #["cache", moduleName.toString, "--json"]
        let args :=
          if roots.size == 1 then
            #["--module", roots[0]!.toString] ++ command
          else command
        let output ← IO.Process.output { cmd := executable.toString, args }
        unless output.exitCode == 0 do
          throw <| IO.userError s!"failed to cache '{moduleName}': {output.stderr.trimAscii.copy}"
        let after ← unsafe Cache.loadPPModule moduleName
        unless names.all after.contains do
          throw <| IO.userError s!"incomplete cache for '{moduleName}'"
        count := count + after.size - before.size
      completed := completed.insert moduleName
      unsafe Cache.savePPProgress roots completed
      progress moduleName (done + 1) pending.size
  unsafe Cache.savePPBundle roots index
  unsafe Cache.markFullyPP roots
  return count

end LeanReach
