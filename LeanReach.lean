import LeanReach.Cache.Build
import LeanReach.Cache.Index
import LeanReach.Cache.PrettyPrint
import LeanReach.Cache.Query
import LeanReach.Query
import LeanReach.Runtime.Environment

namespace LeanReach

open Lean

private def liftStringError {α : Type} (result : Except String α) : IO α :=
  IO.ofExcept (result.mapError IO.userError)

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

private unsafe def prettyPrintMissing (moduleOf? : Name → Option Name)
    (session : Session) (env : Environment) (names : Array Name) : IO Unit := do
  let mut byModule : NameMap (Array Name) := {}
  for name in ← session.missing names do
    if let some moduleName := moduleOf? name then
      byModule := byModule.alter moduleName fun names =>
        some ((names.getD #[]).push name)
  for (moduleName, names) in byModule do
    let (declarations, _) ← unsafe prettyPrintModuleIO
      session.sourcePath env moduleName names moduleOf?
    session.merge declarations

private unsafe def runSession {α : Type} (moduleOf? : Name → Option Name) (session : Session)
    (names : Array Name) (target? : Option Name) (emptyEnv? : Option Environment)
    (action : CoreM α) : IO α := do
  session.merge (← unsafe Cache.loadPP moduleOf? (← session.missing names))
  let before ← session.ppCache
  let targetModule? := target?.bind fun target =>
    if before.contains target then none else moduleOf? target
  let modules := modulesFor moduleOf? (← session.missing names)
  let env ←
    if modules.isEmpty then emptyEnv?.getDM mkEmptyEnvironment
    else importEnvironment modules (leakEnv := emptyEnv?.isNone)
  if let some moduleName := targetModule? then
    unsafe completeTargetModule moduleOf? session env moduleName
  unsafe prettyPrintMissing moduleOf? session env names
  let result ← unsafe runCore env action
  let after ← session.ppCache
  if after.size != before.size then
    try unsafe Cache.savePP before after
    catch _ => IO.eprintln "leanreach: could not write PP sidecar"
  return result

/-- Import only the modules needed to pretty-print the selected declarations. -/
private unsafe def withSessionFor {α β : Type} (roots : Array Name)
    (select : Index → Except String (α × Array Name × Option Name)) (loadRelations : Bool)
    (action : Session → α → CoreM β) : IO β := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex roots loadRelations
  let (plan, names, target?) ← liftStringError (select index)
  let session ← Session.create sourcePath
  unsafe runSession index.moduleOf? session names target? none (action session plan)

private unsafe def runCachedQuery {α : Type} (session : Session)
    (cached : CachedQuery) (names : QueryNames)
    (action : QueryNames → CoreM α) : IO α := do
  unsafe runSession cached.moduleOf? session names.all
    (some names.target) none (action names)

private unsafe def runCachedSearch {α : Type} (session : Session)
    (targets : Array LocatedName) (action : Array Name → CoreM α) : IO α := do
  let names := targets.map (·.name)
  let moduleOf? name := targets.find? (·.name == name) |>.map (·.moduleName)
  unsafe runSession moduleOf? session names none none (action names)

/-- Use the pre-ranked exact-query shard without loading the complete dependency index. -/
unsafe def withCachedQueryFor {α : Type} (roots : Array Name) (query : String)
    (limits : Limits) (action : Session → QueryNames → CoreM α) : IO (Option α) := do
  unless limits.usesCachedQuery do return none
  unsafe prepareSearchPath
  let some cached ← liftStringError (← unsafe QueryCache.resolve roots query) | return none
  let names := cached.queryNames limits
  let session ← unsafe cachedSession cached.moduleOf? names.all
  return some (← unsafe runCachedQuery session cached names (action session))

/-- Search complete declaration names from a query shard without loading the catalog. -/
unsafe def withCachedSearchFor {α : Type} (roots : Array Name) (query : String)
    (limit : Nat) (action : Session → Array Name → CoreM α) : IO (Option α) := do
  unsafe prepareSearchPath
  let some targets ← unsafe QueryCache.search roots query limit | return none
  let names := targets.map (·.name)
  let moduleOf? name := targets.find? (·.name == name) |>.map (·.moduleName)
  let session ← unsafe cachedSession moduleOf? names
  return some (← unsafe runCachedSearch session targets (action session))

/-- Query through a cache shard when available, otherwise load the dependency index. -/
unsafe def withQueryFor {α : Type} (roots : Array Name) (query : String)
    (limits : Limits) (action : Session → QueryNames → CoreM α) : IO α := do
  if let some result ← unsafe withCachedQueryFor roots query limits action then return result
  unsafe withSessionFor roots (fun index => do
    let names ← index.queryNames query limits
    return (names, names.all, some names.target)) true action

/-- Search through cache shards when available, otherwise load the name catalog. -/
unsafe def withSearchFor {α : Type} (roots : Array Name) (query : String)
    (limit : Nat) (action : Session → Array Name → CoreM α) : IO α := do
  if let some result ← unsafe withCachedSearchFor roots query limit action then return result
  unsafe withSessionFor roots (fun index =>
    let names := index.search query limit
    .ok (names, names, none)) false action

structure InteractiveRunner where
  query : String → Limits → (QueryNames → CoreM Unit) → IO Unit
  search : String → Nat → (Array Name → CoreM Unit) → IO Unit

private unsafe def loadIndexOnce (roots : Array Name)
    (cached : IO.Ref (Option Index)) : IO Index := do
  if let some index ← cached.get then return index
  let index ← unsafe Cache.loadIndex roots true
  cached.set (some index)
  return index

unsafe def withInteractiveSession {α : Type} (roots : Array Name)
    (action : Session → InteractiveRunner → IO α) : IO α := do
  let sourcePath ← prepareEnvironment
  let session ← Session.create sourcePath
  let emptyEnv ← mkEmptyEnvironment
  let indexCache ← IO.mkRef none
  let query := fun query limits action => do
    if limits.usesCachedQuery then
      if let some cached ← liftStringError (← unsafe QueryCache.resolve roots query) then
        let names := cached.queryNames limits
        discard <| unsafe runCachedQuery session cached names action
        return
    let index ← unsafe loadIndexOnce roots indexCache
    let names ← liftStringError (index.queryNames query limits)
    discard <| unsafe runSession index.moduleOf? session names.all
      (some names.target) (some emptyEnv) (action names)
  let search := fun pattern limit action => do
    if let some targets ← unsafe QueryCache.search roots pattern limit then
      discard <| unsafe runCachedSearch session targets action
      return
    let index ← unsafe loadIndexOnce roots indexCache
    let names := index.search pattern limit
    discard <| unsafe runSession index.moduleOf? session names none
      (some emptyEnv) (action names)
  action session { query, search }

end LeanReach
