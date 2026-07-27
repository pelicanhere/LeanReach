import Lean.DeclarationRange
import Lean.OriginalConstKind
import LeanReach.Query.Ilean
import LeanReach.Query.Kernel
import LeanReach.Query.Names

namespace LeanReach

open Lean Lean.Core

private def constantKind : ConstantKind → String
  | .axiom => "axiom"
  | .defn => "definition"
  | .thm => "theorem"
  | .opaque => "opaque"
  | .quot => "quotient"
  | .induct => "inductive"
  | .ctor => "constructor"
  | .recursor => "recursor"

private def scoredNames (env : Environment) (query : String) (includeInternal : Bool) :
    Array Query.ScoredName := Id.run do
  let mut hits := #[]
  for (name, _) in env.constants do
    if Query.visibleName includeInternal name then
      if let some score := Query.nameScore query name then
        hits := hits.push (score, name)
  return Query.sortScoredNames hits

private def resolveName (env : Environment) (query : String) (includeInternal : Bool) :
    Except (QueryError Name) Name := do
  let exact := query.toName
  if env.contains exact && Query.visibleName includeInternal exact then
    return exact
  Query.resolveScoredName query (scoredNames env query includeInternal)

def withSession {α : Type} (action : Query.SessionM α) : CoreM α := do
  action.run (← Query.sourceSearchPath)

private def sourceLocation (name : Name) : Query.RequestM SourceLocation := do
  let sourcePath ← readThe SearchPath
  let moduleName? ← findModuleOf? name
  let file? ← match moduleName? with
    | some moduleName => sourcePath.findModuleWithExt "lean" moduleName
    | none => pure none
  let ranges? ← findDeclarationRanges? name
  let (line?, column?, endLine?, endColumn?) := match ranges? with
    | some ranges =>
      (some ranges.selectionRange.pos.line,
       some (ranges.selectionRange.pos.column + 1),
       some ranges.selectionRange.endPos.line,
       some (ranges.selectionRange.endPos.column + 1))
    | none => (none, none, none, none)
  return {
    moduleName := moduleName?.map Query.nameString
    file := file?.map (·.toString)
    line := line?
    column := column?
    endLine := endLine?
    endColumn := endColumn?
  }

private def describeDeclaration (name : Name) : Query.RequestM DeclarationView := do
  let env ← getEnv
  let some kind := getOriginalConstKind? env name |
    throwError "declaration disappeared from the environment: {name}"
  return {
    name := Query.nameString name
    kind := constantKind kind
    source := ← sourceLocation name
  }

private def describeRelations (relations : Array Query.RawRelation) :
    Query.RequestM RelationList := do
  let limit := (← read).limit
  let mut items := #[]
  for relation in relations.take limit do
    items := items.push {
      distance := relation.distance
      via := relation.via.map Query.nameString
      declaration := ← describeDeclaration relation.declaration
    }
  return { total := relations.size, items }

private def executeKernelQuery (query : String) :
    Query.RequestM (Except QueryFailure QueryResult) := do
  let env ← getEnv
  let options ← read
  match resolveName env query options.includeInternal with
  | .error failure =>
    let candidates ← failure.candidates.mapM describeDeclaration
    return .error {
      error := failure.error
      candidates
    }
  | .ok target => do
    let upstream :=
      if options.direction.includesUpstream then
        Query.collectKernelUpstream env target options
      else
        #[]
    let downstream :=
      if options.direction.includesDownstream then
        Query.collectKernelDownstream env target options
      else
        #[]
    return .ok {
      query
      mode := "kernel"
      target := ← describeDeclaration target
      upstream := ← describeRelations upstream
      downstream := ← describeRelations downstream
    }

/-- Run a kernel dependency query inside an existing Environment session. -/
def runKernelQueryM (query : String) (options : QueryOptions := {}) :
    Query.SessionM (Except QueryFailure QueryResult) :=
  (executeKernelQuery query).run { options with mode := .kernel }

/-- Resolve a declaration and inspect its bounded kernel dependency neighborhood. -/
def runKernelQuery (query : String) (options : QueryOptions := {}) :
    CoreM (Except QueryFailure QueryResult) :=
  withSession (runKernelQueryM query options)

private def search (query : String) : Query.RequestM SearchResult := do
  let env ← getEnv
  let options ← read
  let hits := scoredNames env query options.includeInternal
  let mut items := #[]
  for (_, name) in hits.take options.limit do
    items := items.push (← describeDeclaration name)
  return {
    query
    total := hits.size
    items
  }

/-- Search Environment declarations inside an existing session. -/
def runKernelSearchM (query : String) (options : QueryOptions := {}) : Query.SessionM SearchResult :=
  (search query).run options

/-- Search Environment declaration names using exact, suffix, then substring ranking. -/
def runKernelSearch (query : String) (options : QueryOptions := {}) : CoreM SearchResult :=
  withSession (runKernelSearchM query options)

end LeanReach
