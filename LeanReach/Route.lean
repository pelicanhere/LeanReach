import LeanReach.Cache.Index
import LeanReach.PrettyPrint.Module
import LeanReach.Search.Route
import LeanReach.Search.Signature

namespace LeanReach

open Lean

structure RouteRequest where
  anchor : String
  wanted : String
  direction : RouteDirection := .consumers
  maxDepth : Nat := 3
  nodeBudget : Nat := 200
  limit : Nat := 5

structure RouteStep where
  declaration : String
  edgeKind? : Option EdgeKind := none

structure RouteCandidate where
  endpoint : Declaration
  path : Array RouteStep
  signatureMatch : SignatureMatch
  distance : Nat

structure RouteResult where
  anchor : String
  wanted : String
  direction : RouteDirection
  visited : Nat
  truncated : Bool
  results : Array RouteCandidate

def RouteDirection.toString : RouteDirection → String
  | .dependencies => "dependencies"
  | .consumers => "consumers"

def EdgeKind.toString : EdgeKind → String
  | .typeDependency => "type"
  | .bodyDependency => "body"

def SignatureMatchKind.toString : SignatureMatchKind → String
  | .exact => "exact"
  | .applicable => "applicable"
  | .conclusion => "conclusion"
  | .sameHead => "sameHead"
  | .similar => "similar"

instance : ToJson RouteDirection where
  toJson direction := toJson direction.toString

instance : ToJson EdgeKind where
  toJson kind := toJson kind.toString

instance : ToJson SignatureMatchKind where
  toJson kind := toJson kind.toString

instance : ToJson SignatureSimilarity where
  toJson similarity := Json.mkObj [
    ("shared", toJson similarity.shared),
    ("total", toJson similarity.total)
  ]

instance : ToJson SignatureMatch where
  toJson result := Json.mkObj [
    ("kind", toJson result.kind),
    ("coveredInputs", toJson result.coveredInputs),
    ("extraInputs", toJson result.extraInputs),
    ("extraObligations", toJson result.extraObligations),
    ("similarity", toJson result.similarity)
  ]

instance : ToJson RouteStep where
  toJson step := Json.mkObj <| [
    ("declaration", toJson step.declaration)
  ] ++ match step.edgeKind? with
    | none => []
    | some kind => [("edgeKind", toJson kind)]

instance : ToJson RouteCandidate where
  toJson candidate := Json.mkObj [
    ("endpoint", toJson candidate.endpoint),
    ("path", toJson candidate.path),
    ("match", toJson candidate.signatureMatch),
    ("distance", toJson candidate.distance)
  ]

instance : ToJson RouteResult where
  toJson result := Json.mkObj [
    ("anchor", toJson result.anchor),
    ("wanted", toJson result.wanted),
    ("direction", toJson result.direction),
    ("visited", toJson result.visited),
    ("truncated", toJson result.truncated),
    ("results", toJson result.results)
  ]

private def normalizeRequest (request : RouteRequest) : IO RouteRequest := do
  let anchor := request.anchor.trimAscii.copy
  let wanted := request.wanted.trimAscii.copy
  if anchor.isEmpty then throw <| IO.userError "route anchor cannot be empty"
  if wanted.isEmpty then throw <| IO.userError "wanted type cannot be empty"
  if request.nodeBudget == 0 then
    throw <| IO.userError "route node budget must be positive"
  if request.limit == 0 then throw <| IO.userError "route limit must be positive"
  return { request with anchor, wanted }

private def resolveAnchor (index : Index) (source : String) : IO (Name × UInt32) := do
  let candidates := index.exactMatches source 2
  let some target := candidates[0]? |
    throw <| IO.userError s!"unknown route anchor '{source}'"
  if candidates[1]?.isSome then
    throw <| IO.userError s!"ambiguous route anchor '{source}'; use its full name"
  let some id := index.findId? target.name |
    throw <| IO.userError s!"route anchor '{target.name}' is absent from the index"
  return (target.name, id)

private unsafe def scoreCandidates (env : Environment) (index : Index)
    (wanted : String) (names : Array Name) : IO (NameMap SignatureMatch) := do
  -- Elaborate once even when the bounded search finds no endpoints.
  let mut scores : NameMap SignatureMatch := {}
  for (name, score) in ← unsafe scoreSignaturesIO env wanted (names.filter env.contains) do
    scores := scores.insert name score
  let privateNames := names.filter fun name => !env.contains name
  for (moduleName, names) in groupNamesByModule index.moduleOf? privateNames do
    let (batch, _) ← unsafe ModuleData.withPrivateOverlay env moduleName
      names #[] index.moduleOf? fun extended =>
        unsafe scoreSignaturesIO extended wanted names
    for (name, score) in batch do scores := scores.insert name score
  return scores

private structure ScoredEndpoint where
  id : UInt32
  name : Name
  distance : Nat
  signatureMatch : SignatureMatch

private def ScoredEndpoint.betterThan (left right : ScoredEndpoint) : Bool :=
  if left.signatureMatch.betterThan right.signatureMatch then true
  else if right.signatureMatch.betterThan left.signatureMatch then false
  else if left.distance != right.distance then left.distance < right.distance
  else Name.lt left.name right.name

private unsafe def describeNames (sourcePath : SearchPath) (env : Environment)
    (index : Index) (names : Array Name) : IO (NameMap Declaration) := do
  let mut declarations : NameMap Declaration := {}
  for (moduleName, names) in groupNamesByModule index.moduleOf? names do
    let (batch, _) ← unsafe prettyPrintModuleIO
      sourcePath env moduleName names index.moduleOf?
    declarations := declarations.insertMany batch
  return declarations

/-- Find bounded declaration routes whose endpoints best match a Lean type. -/
unsafe def routeFor (roots : Array Name) (request : RouteRequest) : IO RouteResult := do
  let request ← normalizeRequest request
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.materializeIndex roots
  let (anchorName, anchorId) ← resolveAnchor index request.anchor
  let reachable := index.reachable anchorId request.direction
    request.maxDepth request.nodeBudget
  let endpoints := reachable.nodes.extract 1 reachable.nodes.size
  let names := endpoints.map fun (id, _) => (index.locatedAt! id).name
  let env ← importEnvironment roots
  let scores ← unsafe scoreCandidates env index request.wanted names
  let ranked := (endpoints.filterMap fun (id, distance) => do
      let name := (index.locatedAt! id).name
      let signatureMatch ← scores.find? name
      return { id, name, distance, signatureMatch : ScoredEndpoint })
    |>.qsort ScoredEndpoint.betterThan
    |>.take request.limit
  let pathNames := ranked.foldl (init := ({} : NameHashSet)) fun names endpoint =>
    (reachable.pathTo endpoint.id).foldl (init := names) fun names (id, _) =>
      names.insert (index.locatedAt! id).name
  let declarations ← unsafe describeNames sourcePath env index pathNames.toArray
  let results ← ranked.mapM fun endpoint => do
    let some declaration := declarations.find? endpoint.name |
      throw <| IO.userError s!"could not describe route endpoint '{endpoint.name}'"
    let path := (reachable.pathTo endpoint.id).map fun (id, edgeKind?) => {
      declaration := (index.locatedAt! id).name.toString
      edgeKind?
    }
    return {
      endpoint := declaration
      path := path
      signatureMatch := endpoint.signatureMatch
      distance := endpoint.distance
      : RouteCandidate
    }
  return {
    anchor := anchorName.toString
    wanted := request.wanted
    direction := request.direction
    visited := reachable.nodes.size
    truncated := reachable.truncated
    results
  }

end LeanReach
