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
  let missing := names.filter fun name =>
    (declarations.find? name).all (!·.hasSource)
  let sourcePath ← if missing.isEmpty then pure [] else prepareEnvironment
  let session ← Session.create sourcePath
  session.merge declarations
  unsafe runPreparedSession moduleOf? session missing true (action session)

inductive LookupNames where
  | query (names : QueryNames)
  | search (names : Array Name)

def LookupNames.all : LookupNames → Array Name
  | .query names => names.all
  | .search names => names

private structure LookupPlan where
  moduleOf? : Name → Option Name
  result : LookupNames

private def cachedSearchPlan (targets : Array LocatedName) : LookupPlan :=
  let (names, modules) := targets.foldl
    (init := (#[], ({} : NameMap Name)))
    fun (names, modules) target =>
      (names.push target.name, modules.insert target.name target.moduleName)
  { moduleOf? := modules.find?, result := .search names }

private unsafe def selectSearch (roots : Array Name) (pattern : SearchPattern)
    (limit : Nat) (loadIndex : IO Index) : IO LookupPlan := do
  if let some targets ← unsafe QueryCache.search roots pattern limit then
    return cachedSearchPlan targets
  let index ← loadIndex
  return {
    moduleOf? := index.moduleOf?
    result := .search (index.search pattern limit)
  }

private unsafe def selectExact (cached : CachedQuery) (limits : Limits)
    (loadIndex : Bool → IO Index) : IO LookupPlan := do
  if limits.usesCachedQuery then
    return {
      moduleOf? := cached.moduleOf?
      result := .query (cached.queryNames limits)
    }
  let index ← loadIndex true
  return {
    moduleOf? := index.moduleOf?
    result := .query (index.queryNamesAt cached.target.name limits)
  }

private unsafe def selectLookup (roots : Array Name) (source : String)
    (limits : Limits) (loadIndex : Bool → IO Index) : IO LookupPlan := do
  let exactLimit := max 2 limits.search
  if let some exact ← unsafe QueryCache.exactQueries roots source exactLimit then
    if let some cached := exact[0]? then
      if exact[1]?.isNone then
        return ← unsafe selectExact cached limits loadIndex
      return cachedSearchPlan ((exact.take limits.search).map (·.target))
    let pattern ← liftStringError (SearchPattern.compileRegex source)
    return ← unsafe selectSearch roots pattern limits.search (loadIndex false)
  let index ← loadIndex false
  let exact := index.exactMatches source exactLimit
  if let some target := exact[0]? then
    if exact[1]?.isNone then
      let index ← loadIndex true
      return {
        moduleOf? := index.moduleOf?
        result := .query (index.queryNamesAt target.name limits)
      }
    return cachedSearchPlan (exact.take limits.search)
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

abbrev InteractiveRunner :=
  String → Limits → (LookupNames → IO Unit) → IO Unit

private unsafe def loadIndexOnce (roots : Array Name)
    (cached : IO.Ref (Option (Bool × Index))) (loadRelations : Bool) : IO Index := do
  if let some (hasRelations, index) ← cached.get then
    if hasRelations || !loadRelations then return index
  let index ← unsafe Cache.loadIndex roots loadRelations
  cached.set (some (loadRelations, index))
  return index

unsafe def withInteractiveSession {α : Type} (roots : Array Name)
    (action : Session → InteractiveRunner → IO α) : IO α := do
  let sourcePath ← prepareEnvironment
  let session ← Session.create sourcePath
  let indexCache ← IO.mkRef none
  let lookup := fun source limits next => do
    let source ← normalizeQuery source
    let plan ← unsafe selectLookup roots source limits fun loadRelations =>
      unsafe loadIndexOnce roots indexCache loadRelations
    discard <| unsafe runSession plan.moduleOf? session plan.result.all false
      (next plan.result)
  action session lookup

end LeanReach
