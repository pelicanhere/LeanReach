import LeanReach.Query.Names
import LeanReach.SourceIndex.Build
import Std.Data.HashSet

namespace LeanReach.SourceIndex

open Lean

private def scoredNames (index : Index) (query : String) (includeInternal : Bool) :
    Nat → Nat × Array Query.ScoredName := fun capacity => Id.run do
  let scoreName := Query.nameScore query
  let mut total := 0
  let mut buckets : Array (Array Query.ScoredName) := Array.replicate 5 #[]
  for declaration in index.declarations do
    if Query.visibleName includeInternal declaration.name then
      if let some score := scoreName declaration.name declaration.lowerName then
        total := total + 1
        if (buckets[score]!).size < capacity then
          buckets := buckets.modify score (·.push (score, declaration.name))
  return (total, buckets.flatten.take capacity)

private def resolveName (index : Index) (query : String) (includeInternal : Bool) :
    Except (QueryError Name) Name := do
  let exact := query.toName
  if (index.findId? exact).isSome && Query.visibleName includeInternal exact then
    return exact
  Query.resolveScoredName query (scoredNames index query includeInternal 10).2

private def sourceLocation (sourcePath : SearchPath) (declaration : Declaration) :
    IO SourceLocation := do
  let file? ← sourcePath.findModuleWithExt "lean" declaration.module
  let range := declaration.range
  return {
    moduleName := Query.nameString declaration.module
    file := file?.map (·.toString)
    line := range.start.line + 1
    column := range.start.character + 1
    endLine := range.end.line + 1
    endColumn := range.end.character + 1
  }

private def describeDeclaration (index : Index) (sourcePath : SearchPath) (name : Name) :
    IO DeclarationView := do
  let some declaration := index.find? name |
    throw <| IO.userError s!"declaration disappeared from the source index: {Query.nameString name}"
  return {
    name := Query.nameString name
    source := ← sourceLocation sourcePath declaration
  }

private def collectRelations (index : Index) (adjacency : Adjacency)
    (target : Name) (options : QueryOptions) : Array Query.RawRelation := Id.run do
  let some targetId := index.findId? target | return #[]
  let mut visited : Std.HashSet DeclId := ({} : Std.HashSet DeclId).insert targetId
  let mut frontier := #[targetId]
  let mut results := #[]
  for distance in [1:options.depth + 1] do
    let mut next := #[]
    for sourceId in frontier do
      for neighborId in adjacency.neighbors sourceId do
        if !visited.contains neighborId then
          visited := visited.insert neighborId
          next := next.push neighborId
          let neighbor := index.declarations[neighborId]!.name
          if Query.visibleName options.includeInternal neighbor then
            results := results.push {
              declaration := neighbor
              distance
              via := if distance == 1 then none
                else some index.declarations[sourceId]!.name
            }
    frontier := next
    if frontier.isEmpty then
      break
  return results.qsort Query.rawRelationLt

private def describeRelations (index : Index) (sourcePath : SearchPath)
    (options : QueryOptions) (relations : Array Query.RawRelation) : IO RelationList := do
  let items ← (relations.take options.limit).mapM fun relation => do
    return {
      distance := relation.distance
      via := relation.via.map Query.nameString
      declaration := ← describeDeclaration index sourcePath relation.declaration
    }
  return { total := relations.size, items }

/-- Resolve and query a source-visible dependency neighborhood without importing an Environment. -/
def runQuery (index : Index) (sourcePath : SearchPath) (query : String)
    (options : QueryOptions := {}) : IO (Except QueryFailure QueryResult) := do
  match resolveName index query options.includeInternal with
  | .error failure =>
    let candidates ← failure.candidates.mapM (describeDeclaration index sourcePath)
    return .error {
      error := failure.error
      candidates
    }
  | .ok target => do
    let upstream :=
      if options.direction.includesUpstream then
        collectRelations index index.upstream target options
      else
        #[]
    let downstream :=
      if options.direction.includesDownstream then
        collectRelations index index.downstream target options
      else
        #[]
    return .ok {
      query
      target := ← describeDeclaration index sourcePath target
      upstream := ← describeRelations index sourcePath options upstream
      downstream := ← describeRelations index sourcePath options downstream
    }

/-- Search source-visible declaration names without importing an Environment. -/
def runSearch (index : Index) (sourcePath : SearchPath) (query : String)
    (options : QueryOptions := {}) : IO SearchResult := do
  let (total, hits) := scoredNames index query options.includeInternal options.limit
  let items ← (hits.take options.limit).mapM fun (_, name) =>
    describeDeclaration index sourcePath name
  return {
    query
    total
    items
  }

end LeanReach.SourceIndex
