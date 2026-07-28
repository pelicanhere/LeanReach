import LeanReach.Cache
import LeanReach.PP
import LeanReach.Query
import LeanReach.Runtime

namespace LeanReach

open Lean

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
    else importEnvironment modules
  let result ← unsafe runCore env action
  let after ← session.ppCache
  if after.size != before.size then
    try unsafe Cache.savePP before after
    catch _ => IO.eprintln "leanreach: could not write PP sidecar"
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

end LeanReach
