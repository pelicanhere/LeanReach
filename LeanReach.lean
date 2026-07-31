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

private unsafe def prepareMissing (moduleOf? : Name → Option Name)
    (session : Session) (missing : Array Name) (leakEnv : Bool) : IO Unit := do
  let byModule := groupNamesByModule moduleOf? missing
  unless byModule.isEmpty do
    let env ← importEnvironment byModule.keysArray (leakEnv := leakEnv)
    for (moduleName, names) in byModule do
      let (declarations, _) ← unsafe prettyPrintModuleIO
        session.sourcePath env moduleName names moduleOf?
      session.merge declarations
      try unsafe Cache.mergePPModule moduleName declarations
      catch _ => IO.eprintln "leanreach: could not write PP sidecar"

private unsafe def prepareSession (moduleOf? : Name → Option Name) (session : Session)
    (names : Array Name) (leakEnv : Bool) : IO Unit := do
  let missing ← session.missing names
  session.merge (← unsafe Cache.loadPP moduleOf? missing)
  unsafe prepareMissing moduleOf? session (← session.missing missing) leakEnv

private unsafe def withFreshSession {α : Type} (moduleOf? : Name → Option Name)
    (names : Array Name) (action : Session → IO α) : IO α := do
  let declarations ← unsafe Cache.loadPP moduleOf? names
  let missing := Declaration.missingFrom declarations names
  let sourcePath ← if missing.isEmpty then pure [] else prepareEnvironment
  let session ← Session.create sourcePath
  session.merge declarations
  unsafe prepareMissing moduleOf? session missing true
  action session

inductive LookupNames where
  | query (names : QueryNames)
  | search (names : Array Name)

private def LookupNames.all : LookupNames → Array Name
  | .query names => names.all
  | .search names => names

private structure LookupPlan where
  moduleOf? : Name → Option Name
  result : LookupNames

private def cachedSearchPlan (targets : Array LocatedName) : LookupPlan :=
  let modules : NameMap Name := ({} : NameMap Name).insertMany <|
    targets.map fun target => (target.name, target.moduleName)
  { moduleOf? := modules.find?, result := .search (targets.map (·.name)) }

private unsafe def selectSearch (roots : Array Name) (pattern : SearchPattern)
    (limit : Nat) (loadIndex : IO Index) : IO LookupPlan := do
  if let some targets ← unsafe QueryCache.search roots pattern limit then
    return cachedSearchPlan targets
  let index ← loadIndex
  return {
    moduleOf? := index.moduleOf?
    result := .search (index.search pattern limit)
  }

private unsafe def selectLookup (roots : Array Name) (source : String)
    (limits : Limits) (loadIndex : IO Index) : IO LookupPlan := do
  let exactLimit := max 2 limits.search
  if let some exact ← unsafe QueryCache.exactQueries roots source
      { limits with search := exactLimit } then
    if let some cached := exact[0]? then
      if exact[1]?.isNone then
        return {
          moduleOf? := cached.moduleOf?
          result := .query (cached.queryNames limits)
        }
      return cachedSearchPlan ((exact.take limits.search).map (·.target))
    let pattern ← liftStringError (SearchPattern.compileRegex source)
    return ← unsafe selectSearch roots pattern limits.search loadIndex
  let index ← loadIndex
  let exact := index.exactMatches source exactLimit
  if let some target := exact[0]? then
    if exact[1]?.isNone then
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
  let plan ← unsafe selectLookup roots source limits
    (unsafe Cache.materializeIndex roots)
  unsafe withFreshSession plan.moduleOf? plan.result.all fun session =>
    action session plan.result

abbrev InteractiveRunner :=
  String → Limits → (LookupNames → IO Unit) → IO Unit

private unsafe def loadIndexOnce (roots : Array Name)
    (cached : IO.Ref (Option Index)) : IO Index := do
  if let some index ← cached.get then return index
  let index ← unsafe Cache.materializeIndex roots
  cached.set (some index)
  return index

unsafe def withInteractiveSession {α : Type} (roots : Array Name)
    (action : Session → InteractiveRunner → IO α) : IO α := do
  let sourcePath ← prepareEnvironment
  let session ← Session.create sourcePath
  let indexCache ← IO.mkRef none
  let lookup := fun source limits next => do
    let source ← normalizeQuery source
    let plan ← unsafe selectLookup roots source limits
      (unsafe loadIndexOnce roots indexCache)
    unsafe prepareSession plan.moduleOf? session plan.result.all false
    next plan.result
  action session lookup

end LeanReach
