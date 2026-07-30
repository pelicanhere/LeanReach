import LeanReach.Cache.Build
import LeanReach.Cache.Index
import LeanReach.Cache.PrettyPrint
import LeanReach.Cache.Query
import LeanReach.Query
import LeanReach.Runtime.Environment

namespace LeanReach

open Lean

abbrev SessionPlan (α : Type) := α × Array Name × Option Name

private def selectPlan {α : Type} (index : Index)
    (select : Index → Except String (SessionPlan α)) : IO (SessionPlan α) :=
  match select index with
  | .ok plan => pure plan
  | .error message => throw <| IO.userError message

private def modulesFor (moduleOf? : Name → Option Name) (names : Array Name) :
    Array Name :=
  (names.toList.filterMap moduleOf?).eraseDups.toArray

private unsafe def cachedSession (moduleOf? : Name → Option Name)
    (names : Array Name) : IO Session := do
  let declarations ← unsafe Cache.loadPP moduleOf? names
  let sourcePath ←
    if names.all declarations.contains then pure []
    else prepareEnvironment
  let session ← Session.create sourcePath
  session.merge declarations
  return session

private def targetModuleCacheLimit := 512

private unsafe def completeTargetModule (moduleOf? : Name → Option Name)
    (session : Session) (env : Environment) (moduleName : Name) : IO Unit := do
  let names ← unsafe Cache.moduleNames moduleName
  if names.size > targetModuleCacheLimit then return
  let cached ← unsafe Cache.loadPPModule moduleName
  let missing := names.filter fun name => !cached.contains name
  if missing.isEmpty then return
  try
    let (declarations, _) ← unsafe prettyPrintModuleIO
      session.sourcePath env moduleName missing moduleOf?
    session.merge declarations
  catch _ => pure ()

private unsafe def runSession {α : Type} (moduleOf? : Name → Option Name) (session : Session)
    (names : Array Name) (target? : Option Name) (modules? : Option (Array Name))
    (wholeModules : Bool) (emptyEnv? : Option Environment) (action : CoreM α) : IO α := do
  let missing ← session.missing names
  if wholeModules then
    for moduleName in modulesFor moduleOf? missing do
      session.merge (← unsafe Cache.loadPPModule moduleName)
  else
    session.merge (← unsafe Cache.loadPP moduleOf? missing)
  let before ← session.ppCache
  let targetModule? := target?.bind fun target =>
    if before.contains target then none else moduleOf? target
  let modules := modules?.getD <|
    modulesFor moduleOf? (← session.missing names)
  let env ←
    if modules.isEmpty then emptyEnv?.getDM mkEmptyEnvironment
    else importEnvironment modules (leakEnv := emptyEnv?.isNone)
  if let some moduleName := targetModule? then
    unsafe completeTargetModule moduleOf? session env moduleName
  let result ← unsafe runCore env action
  let after ← session.ppCache
  if after.size != before.size then
    try unsafe Cache.savePP before after
    catch _ => IO.eprintln "leanreach: could not write PP sidecar"
  return result

private unsafe def withIndexSession {α β : Type} (roots : Array Name)
    (loadRelations : Bool)
    (select : Index → Except String (SessionPlan α))
    (forceRootImport : Bool)
    (action : Index → Session → α → CoreM β) : IO β := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex roots loadRelations
  let (plan, names, target?) ← selectPlan index select
  let session ← Session.create sourcePath
  unsafe runSession index.moduleOf? session names target?
    (if forceRootImport then some roots else none) false none (action index session plan)

/-- Import only the modules needed to pretty-print the selected declarations. -/
unsafe def withSessionFor {α β : Type} (roots : Array Name)
    (select : Index → Except String (SessionPlan α)) (loadRelations : Bool)
    (action : Session → α → CoreM β) : IO β :=
  withIndexSession roots loadRelations select false fun _ => action

/-- Use the pre-ranked exact-query shard without loading the complete dependency index. -/
unsafe def withCachedQueryFor {α : Type} (roots : Array Name) (query : String)
    (limits : Limits) (action : Session → QueryNames → CoreM α) : IO (Option α) := do
  unless limits.usesCachedQuery do return none
  unsafe prepareSearchPath
  let cached? ← unsafe QueryCache.resolve roots query
  let cached ← match cached? with
    | .ok (some cached) => pure cached
    | .ok none => return none
    | .error message => throw <| IO.userError message
  let names := cached.queryNames limits
  let session ← unsafe cachedSession cached.moduleOf? names.all
  return some (← unsafe runSession cached.moduleOf? session names.all
    (some names.target) none false none
    (action session names))

/-- Search complete declaration names from a query shard without loading the catalog. -/
unsafe def withCachedSearchFor {α : Type} (roots : Array Name) (query : String)
    (limit : Nat) (action : Session → Array Name → CoreM α) : IO (Option α) := do
  unsafe prepareSearchPath
  let some targets ← unsafe QueryCache.search roots query limit | return none
  let names := targets.map (·.name)
  let moduleOf? name := targets.find? (·.name == name) |>.map (·.moduleName)
  let session ← unsafe cachedSession moduleOf? names
  return some (← unsafe runSession moduleOf? session names none none false none
    (action session names))

/-- Import the root modules once and reuse their environment and index for the entire action. -/
unsafe def withSession {α : Type} (roots : Array Name)
    (action : Index → Session → CoreM α) : IO α :=
  withIndexSession roots true (fun _ => pure ((), #[], none)) true fun index session _ =>
    action index session

abbrev SessionRunner :=
  {α : Type} → (Index → Except String (SessionPlan α)) →
    (α → CoreM Unit) → IO Unit

unsafe def withLazySession {α : Type} (roots : Array Name)
    (action : Session → SessionRunner → IO α) : IO α := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex roots true
  let session ← Session.create sourcePath
  let emptyEnv ← mkEmptyEnvironment
  let run : SessionRunner := fun select query => do
    let (plan, names, target?) ← selectPlan index select
    discard <| unsafe runSession index.moduleOf? session names target? none true
      (some emptyEnv) (query plan)
  action session run

end LeanReach
