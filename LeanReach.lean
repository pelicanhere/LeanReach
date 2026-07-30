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
    (names : Array Name) : IO (Session × Array Name) := do
  let declarations ← unsafe Cache.loadPP moduleOf? names
  let missing := names.filter fun name => !declarations.contains name
  let sourcePath ←
    if missing.isEmpty then pure []
    else prepareEnvironment
  let session ← Session.create sourcePath
  session.merge declarations
  return (session, missing)

private unsafe def prettyPrintMissing (moduleOf? : Name → Option Name)
    (session : Session) (env : Environment) (names : Array Name) :
    IO (NameMap Declaration) := do
  let mut byModule : NameMap (Array Name) := {}
  for name in names do
    if let some moduleName := moduleOf? name then
      byModule := byModule.alter moduleName fun names =>
        some ((names.getD #[]).push name)
  let mut added := {}
  for (moduleName, names) in byModule do
    let (declarations, _) ← unsafe prettyPrintModuleIO
      session.sourcePath env moduleName names moduleOf?
    session.merge declarations
    added := Std.TreeMap.union added declarations
  return added

private unsafe def runPreparedSession {α : Type} (moduleOf? : Name → Option Name)
    (session : Session) (missing : Array Name) (leakEnv : Bool)
    (action : IO α) : IO α := do
  let mut added := {}
  unless missing.isEmpty do
    let modules := modulesFor moduleOf? missing
    unless modules.isEmpty do
      let env ← importEnvironment modules (leakEnv := leakEnv)
      added ← unsafe prettyPrintMissing moduleOf? session env missing
  unless added.isEmpty do
    try unsafe Cache.savePP added
    catch _ => IO.eprintln "leanreach: could not write PP sidecar"
  action

private unsafe def runSession {α : Type} (moduleOf? : Name → Option Name) (session : Session)
    (names : Array Name) (leakEnv : Bool) (action : IO α) : IO α := do
  session.merge (← unsafe Cache.loadPP moduleOf? (← session.missing names))
  unsafe runPreparedSession moduleOf? session (← session.missing names) leakEnv action

/-- Import only the modules needed to pretty-print the selected declarations. -/
private unsafe def withSessionFor {α β : Type} (roots : Array Name)
    (select : Index → Except String (α × Array Name)) (loadRelations : Bool)
    (action : Session → α → IO β) : IO β := do
  let index ← unsafe Cache.loadIndex roots loadRelations
  let (plan, names) ← liftStringError (select index)
  let (session, missing) ← unsafe cachedSession index.moduleOf? names
  unsafe runPreparedSession index.moduleOf? session missing true (action session plan)

private def cachedSearchPlan (targets : Array LocatedName) : Array Name × NameMap Name :=
  targets.foldl (init := (#[], {})) fun (names, modules) target =>
    (names.push target.name, modules.insert target.name target.moduleName)

/-- Use the pre-ranked exact-query shard without loading the complete dependency index. -/
unsafe def withCachedQueryFor {α : Type} (roots : Array Name) (query : String)
    (limits : Limits) (action : Session → QueryNames → IO α) : IO (Option α) := do
  unless limits.usesCachedQuery do return none
  unsafe prepareSearchPath
  let some cached ← liftStringError (← unsafe QueryCache.resolve roots query) | return none
  let names := cached.queryNames limits
  let (session, missing) ← unsafe cachedSession cached.moduleOf? names.all
  return some (← unsafe runPreparedSession cached.moduleOf? session missing true
    (action session names))

/-- Search complete declaration names from a query shard without loading the catalog. -/
unsafe def withCachedSearchFor {α : Type} (roots : Array Name) (query : String)
    (limit : Nat) (action : Session → Array Name → IO α) : IO (Option α) := do
  unsafe prepareSearchPath
  let some targets ← unsafe QueryCache.search roots query limit | return none
  let (names, modules) := cachedSearchPlan targets
  let (session, missing) ← unsafe cachedSession modules.find? names
  return some (← unsafe runPreparedSession modules.find? session missing true
    (action session names))

/-- Query through a cache shard when available, otherwise load the dependency index. -/
unsafe def withQueryFor {α : Type} (roots : Array Name) (query : String)
    (limits : Limits) (action : Session → QueryNames → IO α) : IO α := do
  if let some result ← unsafe withCachedQueryFor roots query limits action then return result
  unsafe withSessionFor roots (fun index => do
    let names ← index.queryNames query limits
    return (names, names.all)) true action

/-- Search through cache shards when available, otherwise load the name catalog. -/
unsafe def withSearchFor {α : Type} (roots : Array Name) (query : String)
    (limit : Nat) (action : Session → Array Name → IO α) : IO α := do
  if let some result ← unsafe withCachedSearchFor roots query limit action then return result
  unsafe withSessionFor roots (fun index =>
    let names := index.search query limit
    .ok (names, names)) false action

structure InteractiveRunner where
  query : String → Limits → (QueryNames → IO Unit) → IO Unit
  search : String → Nat → (Array Name → IO Unit) → IO Unit

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
  let indexCache ← IO.mkRef none
  let query := fun query limits action => do
    if limits.usesCachedQuery then
      if let some cached ← liftStringError (← unsafe QueryCache.resolve roots query) then
        let names := cached.queryNames limits
        discard <| unsafe runSession cached.moduleOf? session names.all false (action names)
        return
    let index ← unsafe loadIndexOnce roots indexCache
    let names ← liftStringError (index.queryNames query limits)
    discard <| unsafe runSession index.moduleOf? session names.all false (action names)
  let search := fun pattern limit action => do
    if let some targets ← unsafe QueryCache.search roots pattern limit then
      let (names, modules) := cachedSearchPlan targets
      discard <| unsafe runSession modules.find? session names false (action names)
      return
    let index ← unsafe loadIndexOnce roots indexCache
    let names := index.search pattern limit
    discard <| unsafe runSession index.moduleOf? session names false (action names)
  action session { query, search }

end LeanReach
