import LeanReach.Query.Names
import LeanReach.Query.Ilean
import LeanReach.SourceIndex.Build

namespace LeanReach.SourceIndex

open Lean

private def scoredNames (index : Index) (query : String) (includeInternal : Bool) :
    Array Query.ScoredName := Id.run do
  let mut hits := #[]
  for (name, _) in index.declarations do
    if Query.visibleName includeInternal name then
      if let some score := Query.nameScore query name then
        hits := hits.push (score, name)
  return Query.sortScoredNames hits

private def resolveName (index : Index) (query : String) (includeInternal : Bool) :
    Except (QueryError Name) Name := do
  let exact := query.toName
  if index.declarations.contains exact && Query.visibleName includeInternal exact then
    return exact
  Query.resolveScoredName query (scoredNames index query includeInternal)

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
  let some declaration := index.declarations.find? name |
    throw <| IO.userError s!"declaration disappeared from the source index: {Query.nameString name}"
  return {
    name := Query.nameString name
    source := ← sourceLocation sourcePath declaration
  }

private def collectUpstream (index : Index) (target : Name) (options : QueryOptions) :
    IO (Array Query.RawRelation) := do
  let mut cache : NameMap Server.Ilean := {}
  let mut visited : NameSet := ({} : NameSet).insert target
  let mut frontier := #[target]
  let mut results := #[]
  for distance in [1:options.depth + 1] do
    let mut next := #[]
    for parent in frontier do
      let some declaration := index.declarations.find? parent | continue
      let ilean? ← match cache.find? declaration.module with
        | some ilean => pure (some ilean)
        | none => do
          let loaded ← Query.loadIlean? declaration.module
          if let some ilean := loaded then
            cache := cache.insert declaration.module ilean
          pure loaded
      let some ilean := ilean? | continue
      for dependency in Query.sourceDependencies ilean parent do
        if index.declarations.contains dependency && !visited.contains dependency then
          visited := visited.insert dependency
          next := next.push dependency
          if Query.visibleName options.includeInternal dependency then
            results := results.push {
              declaration := dependency
              distance
              via := if distance == 1 then none else some parent
            }
    frontier := next
    if frontier.isEmpty then
      break
  return results.qsort Query.rawRelationLt

private def collectDownstream (index : Index) (target : Name) (options : QueryOptions) :
    Array Query.RawRelation := Id.run do
  let mut visited : NameSet := ({} : NameSet).insert target
  let mut frontier : NameSet := ({} : NameSet).insert target
  let mut results := #[]
  for distance in [1:options.depth + 1] do
    let mut next : NameSet := {}
    for dependency in frontier do
      let some parents := index.downstream.find? dependency | continue
      for parent in parents do
        if index.declarations.contains parent && !visited.contains parent then
          visited := visited.insert parent
          next := next.insert parent
          if Query.visibleName options.includeInternal parent then
            results := results.push {
              declaration := parent
              distance
              via := if distance == 1 then none else some dependency
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
    let upstream ←
      if options.direction.includesUpstream then
        collectUpstream index target options
      else
        pure #[]
    let downstream :=
      if options.direction.includesDownstream then
        collectDownstream index target options
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
  let hits := scoredNames index query options.includeInternal
  let items ← (hits.take options.limit).mapM fun (_, name) =>
    describeDeclaration index sourcePath name
  return {
    query
    total := hits.size
    items
  }

end LeanReach.SourceIndex
