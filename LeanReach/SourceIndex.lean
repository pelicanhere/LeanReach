import LeanReach.Query.Names
import LeanReach.Signatures
import LeanReach.SourceIndex.Build
import Std.Data.HashSet

namespace LeanReach.SourceIndex

open Lean

structure Session where
  index : Index
  sourcePath : SearchPath
  private signatures : IO.Ref (NameMap String)
  private sourceFiles : IO.Ref (NameMap (Option String))

def Session.create (index : Index) (sourcePath : SearchPath) : IO Session := do
  return {
    index
    sourcePath
    signatures := ← IO.mkRef {}
    sourceFiles := ← IO.mkRef {}
  }

private def scoredNames (index : Index) (query : String) (includeInternal : Bool) :
    Nat → Nat × Array Query.ScoredName := fun capacity => Id.run do
  let scoreName := Query.nameScore query
  let queryFilter? := Query.trigramFilter? query.toLower
  let mut total := 0
  let mut buckets : Array (Array Query.ScoredName) := Array.replicate 5 #[]
  for declaration in index.declarations do
    let mayContain := match queryFilter? with
      | some queryFilter =>
        declaration.trigramFilter &&& queryFilter == queryFilter
      | none => true
    if mayContain && Query.visibleName includeInternal declaration.name then
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

private def sourceLocation (session : Session) (declaration : Declaration) :
    IO SourceLocation := do
  let files ← session.sourceFiles.get
  let file? ← match files.find? declaration.module with
    | some file? => pure file?
    | none => do
      let file? :=
        (← session.sourcePath.findModuleWithExt "lean" declaration.module).map (·.toString)
      session.sourceFiles.set (files.insert declaration.module file?)
      pure file?
  let range := declaration.range
  return {
    moduleName := Query.nameString declaration.module
    file := file?
    line := range.start.line + 1
    column := range.start.character + 1
    endLine := range.end.line + 1
    endColumn := range.end.character + 1
  }

private unsafe def preloadSignatures (session : Session) (names : Array Name) : IO Unit := do
  let mut signatures ← session.signatures.get
  let mut pending : NameMap NameSet := {}
  for name in names do
    unless signatures.contains name do
      if let some declaration := session.index.find? name then
        pending := pending.alter declaration.module fun names? =>
          some ((names?.getD {}).insert name)
  for (moduleName, moduleNames) in pending do
    let loaded ← unsafe Signatures.load moduleName moduleNames
    for name in moduleNames do
      signatures := signatures.insert name
        ((loaded.find? name).getD (Signatures.unavailable name))
  session.signatures.set signatures

private def describeDeclaration (session : Session) (name : Name) :
    IO DeclarationView := do
  let some declaration := session.index.find? name |
    throw <| IO.userError s!"declaration disappeared from the source index: {Query.nameString name}"
  let signatures ← session.signatures.get
  return {
    name := Query.nameString name
    signature := (signatures.find? name).getD (Signatures.unavailable name)
    source := ← sourceLocation session declaration
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

private def describeRelations (session : Session)
    (options : QueryOptions) (relations : Array Query.RawRelation) : IO RelationList := do
  let items ← (relations.take options.limit).mapM fun relation => do
    return {
      distance := relation.distance
      via := relation.via.map Query.nameString
      declaration := ← describeDeclaration session relation.declaration
    }
  return { total := relations.size, items }

/-- Resolve and query a source-visible dependency neighborhood without importing an Environment. -/
unsafe def runQuery (session : Session) (query : String)
    (options : QueryOptions := {}) : IO (Except QueryFailure QueryResult) := do
  let index := session.index
  match resolveName index query options.includeInternal with
  | .error failure =>
    unsafe preloadSignatures session failure.candidates
    let candidates ← failure.candidates.mapM (describeDeclaration session)
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
    let resultNames := #[target] ++
      (upstream.take options.limit).map (·.declaration) ++
      (downstream.take options.limit).map (·.declaration)
    unsafe preloadSignatures session resultNames
    return .ok {
      query
      target := ← describeDeclaration session target
      upstream := ← describeRelations session options upstream
      downstream := ← describeRelations session options downstream
    }

/-- Search source-visible declaration names without importing an Environment. -/
unsafe def runSearch (session : Session) (query : String)
    (options : QueryOptions := {}) : IO SearchResult := do
  let (total, hits) :=
    scoredNames session.index query options.includeInternal options.limit
  unsafe preloadSignatures session (hits.map (·.2))
  let items ← (hits.take options.limit).mapM fun (_, name) =>
    describeDeclaration session name
  return {
    query
    total
    items
  }

end LeanReach.SourceIndex
