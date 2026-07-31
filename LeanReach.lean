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

private def normalizeQuery (query : String) : IO String := do
  let query := query.trimAscii.copy
  if query.isEmpty then throw <| IO.userError "declaration query cannot be empty"
  return query

private def groupByModule (moduleOf? : Name → Option Name) (names : Array Name) :
    Array Name × NameMap (Array Name) := Id.run do
  let mut modules := #[]
  let mut byModule := {}
  for name in names do
    if let some moduleName := moduleOf? name then
      unless byModule.contains moduleName do
        modules := modules.push moduleName
      byModule := byModule.alter moduleName fun names =>
        some ((names.getD #[]).push name)
  return (modules, byModule)

private unsafe def prettyPrintMissing (moduleOf? : Name → Option Name)
    (sourcePath : SearchPath) (env : Environment)
    (byModule : NameMap (Array Name)) :
    IO Cache.PPBatch := do
  let mut added := {}
  for (moduleName, names) in byModule do
    let (declarations, _) ← unsafe prettyPrintModuleIO
      sourcePath env moduleName names moduleOf?
    added := added.insert moduleName declarations
  return added

private unsafe def runPreparedSession {α : Type} (moduleOf? : Name → Option Name)
    (session : Session) (missing : Array Name) (leakEnv : Bool)
    (action : IO α) : IO α := do
  let mut added := {}
  let (modules, byModule) := groupByModule moduleOf? missing
  unless modules.isEmpty do
    let env ← importEnvironment modules (leakEnv := leakEnv)
    added ← unsafe prettyPrintMissing moduleOf? session.sourcePath env byModule
  unless added.isEmpty do
    for (_, declarations) in added do session.merge declarations
    try unsafe Cache.savePP added
    catch _ => IO.eprintln "leanreach: could not write PP sidecar"
  action

private unsafe def runSession {α : Type} (moduleOf? : Name → Option Name) (session : Session)
    (names : Array Name) (leakEnv : Bool) (action : IO α) : IO α := do
  let missing ← session.missing names
  session.merge (← unsafe Cache.loadPP moduleOf? missing)
  unsafe runPreparedSession moduleOf? session
    (← session.missing missing) leakEnv action

private unsafe def withFreshSession {α : Type} (moduleOf? : Name → Option Name)
    (names : Array Name) (action : Session → IO α) : IO α := do
  let declarations ← unsafe Cache.loadPP moduleOf? names
  let missing := names.filter fun name => !declarations.contains name
  let sourcePath ← if missing.isEmpty then pure [] else prepareEnvironment
  let session ← Session.create sourcePath
  session.merge declarations
  unsafe runPreparedSession moduleOf? session missing true (action session)

/-- Import only the modules needed to pretty-print the selected declarations. -/
private unsafe def withSessionFor {α β : Type} (roots : Array Name)
    (select : Index → Except String (α × Array Name)) (loadRelations : Bool)
    (action : Session → α → IO β) : IO β := do
  let index ← unsafe Cache.loadIndex roots loadRelations
  let (plan, names) ← liftStringError (select index)
  unsafe withFreshSession index.moduleOf? names fun session => action session plan

private def cachedSearchPlan (targets : Array LocatedName) : Array Name × NameMap Name :=
  targets.foldl (init := (#[], {})) fun (names, modules) target =>
    (names.push target.name, modules.insert target.name target.moduleName)

inductive LookupNames where
  | query (names : QueryNames)
  | search (names : Array Name)

def LookupNames.all : LookupNames → Array Name
  | .query names => names.all
  | .search names => names

private structure LookupPlan where
  moduleOf? : Name → Option Name
  result : LookupNames

/-- Resolve through cache shards, loading the dependency index only when relations require it. -/
unsafe def withQueryFor {α : Type} (roots : Array Name) (query : String)
    (limits : Limits) (action : Session → QueryNames → IO α) : IO α := do
  let query ← normalizeQuery query
  unsafe prepareSearchPath
  if let some cached ← liftStringError (← unsafe QueryCache.resolve roots query) then
    if limits.usesCachedQuery then
      let names := cached.queryNames limits
      return ← unsafe withFreshSession cached.moduleOf? names.all fun session =>
        action session names
  unsafe withSessionFor roots (fun index => do
    let names ← index.queryNames query limits
    return (names, names.all)) true action

private unsafe def selectSearch (roots : Array Name) (pattern : SearchPattern)
    (limit : Nat) (loadIndex : IO Index) :
    IO ((Name → Option Name) × Array Name) := do
  if let some targets ← unsafe QueryCache.search roots pattern limit then
    let (names, modules) := cachedSearchPlan targets
    return (modules.find?, names)
  let index ← loadIndex
  return (index.moduleOf?, index.search pattern limit)

private def matchPlan (targets : Array LocatedName) : LookupPlan :=
  let (names, modules) := cachedSearchPlan targets
  { moduleOf? := modules.find?, result := .search names }

private unsafe def selectExact (roots : Array Name) (target : LocatedName)
    (limits : Limits) (loadIndex : Bool → IO Index) : IO LookupPlan := do
  if limits.usesCachedQuery then
    if let .ok (some cached) ←
        unsafe QueryCache.resolve roots target.name.toString then
      return {
        moduleOf? := cached.moduleOf?
        result := .query (cached.queryNames limits)
      }
  let index ← loadIndex true
  return {
    moduleOf? := index.moduleOf?
    result := .query (index.queryNamesAt target.name limits)
  }

private unsafe def selectLookup (roots : Array Name) (source : String)
    (limits : Limits) (loadIndex : Bool → IO Index) : IO LookupPlan := do
  let exactLimit := max 2 limits.search
  if let some exact ← unsafe QueryCache.exactMatches roots source exactLimit then
    if let some target := exact[0]? then
      if exact[1]?.isNone then
        return ← unsafe selectExact roots target limits loadIndex
      return matchPlan (exact.take limits.search)
    let pattern ← liftStringError (SearchPattern.compileRegex source)
    let (moduleOf?, names) ← unsafe selectSearch roots pattern limits.search
      (loadIndex false)
    return { moduleOf?, result := .search names }
  let index ← loadIndex false
  let exact := index.exactMatches source exactLimit
  if let some target := exact[0]? then
    if exact[1]?.isNone then
      return ← unsafe selectExact roots target limits loadIndex
    return matchPlan (exact.take limits.search)
  let pattern ← liftStringError (SearchPattern.compileRegex source)
  return {
    moduleOf? := index.moduleOf?
    result := .search (index.search pattern limits.search)
  }

/-- Query an exact declaration name, otherwise search the same input as a regex. -/
unsafe def withLookupFor {α : Type} (roots : Array Name) (source : String)
    (limits : Limits) (action : Session → LookupNames → IO α) : IO α := do
  let source ← normalizeQuery source
  unsafe prepareSearchPath
  let plan ← unsafe selectLookup roots source limits fun loadRelations =>
    unsafe Cache.loadIndex roots loadRelations
  unsafe withFreshSession plan.moduleOf? plan.result.all fun session =>
    action session plan.result

/-- Search through cache shards when available, otherwise load the name catalog. -/
unsafe def withSearchFor {α : Type} (roots : Array Name) (pattern : SearchPattern)
    (limit : Nat) (action : Session → Array Name → IO α) : IO α := do
  unsafe prepareSearchPath
  let (moduleOf?, names) ← unsafe selectSearch roots pattern limit
    (unsafe Cache.loadIndex roots false)
  unsafe withFreshSession moduleOf? names fun session => action session names

structure InteractiveRunner where
  lookup : String → Limits → (LookupNames → IO Unit) → IO Unit

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
  let lookup := fun source limits next => do
    let source ← normalizeQuery source
    let plan ← unsafe selectLookup roots source limits fun _ =>
      unsafe loadIndexOnce roots indexCache
    discard <| unsafe runSession plan.moduleOf? session plan.result.all false
      (next plan.result)
  action session { lookup }

end LeanReach
