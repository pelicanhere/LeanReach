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
  beamWidth : Nat := 20
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
  if wanted.isEmpty then
    throw <| IO.userError "wanted type or declaration cannot be empty"
  if request.nodeBudget == 0 then
    throw <| IO.userError "route node budget must be positive"
  if request.beamWidth == 0 then
    throw <| IO.userError "route beam width must be positive"
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

private def quotedName? (env : Environment) (source : String) : IO (Option String) := do
  let stx ← match Parser.runParserCategory env `term source "<wanted>" with
    | .ok stx => pure stx
    | .error message => throw <| IO.userError message
  match stx with
  | `($value:str) => return some value.getString
  | _ => return none

private def resolveWantedDeclaration (index : Index)
    (source : String) : IO (LocatedName × UInt32) := do
  let candidates := index.exactMatches source 2
  let some target := candidates[0]? |
    throw <| IO.userError s!"unknown wanted declaration '{source}'"
  if candidates[1]?.isSome then
    throw <| IO.userError s!"ambiguous wanted declaration '{source}'; use its full name"
  let some id := index.findId? target.name |
    throw <| IO.userError s!"wanted declaration '{target.name}' is absent from the index"
  return (target, id)

private structure WantedTarget where
  type : Expr
  declaration? : Option UInt32 := none

private unsafe def withWantedTarget {α : Type} (env : Environment) (index : Index)
    (source : String) (action : Environment → WantedTarget → IO α) : IO α := do
  let some declaration ← quotedName? env source | do
    action env { type := ← unsafe elaborateSignatureIO env source }
  let (target, id) ← resolveWantedDeclaration index declaration
  let run := fun env => do
    let some info := env.find? target.name |
      throw <| IO.userError s!"could not load wanted declaration '{declaration}'"
    action env { type := info.type, declaration? := some id }
  if env.contains target.name then return ← run env
  return (← unsafe ModuleData.withPrivateOverlay env target.moduleName
    #[target.name] #[] index.moduleOf? run).1

private unsafe def scoreCandidates (env : Environment) (index : Index)
    (wantedType : Expr) (names : Array Name) : IO (NameMap SignatureMatch) := do
  let mut scores : NameMap SignatureMatch := {}
  for (name, score) in ← unsafe scoreSignaturesIO
      env wantedType (names.filter env.contains) do
    scores := scores.insert name score
  let privateNames := names.filter fun name => !env.contains name
  for (moduleName, names) in groupNamesByModule index.moduleOf? privateNames do
    let (batch, _) ← unsafe ModuleData.withPrivateOverlay env moduleName
      names #[] index.moduleOf? fun extended =>
        unsafe scoreSignaturesIO extended wantedType names
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

private unsafe def beamReachable (env : Environment) (index : Index)
    (anchor : UInt32) (wantedType : Expr) (request : RouteRequest) :
    IO (Reachability × NameMap SignatureMatch) := do
  let mut seen := Array.replicate index.size false
  let mut predecessors : Array (Option RoutePredecessor) :=
    Array.replicate index.size none
  let mut nodes := #[(anchor, 0)]
  let mut frontier := #[anchor]
  let mut scores : NameMap SignatureMatch := {}
  let mut depth := 0
  let mut truncated := false
  seen := seen.set! anchor.toNat true
  while !frontier.isEmpty && depth < request.maxDepth && !truncated do
    let nextDepth := depth + 1
    let mut discovered : Array UInt32 := #[]
    for source in frontier do
      if truncated then break
      for (target, edgeKind) in index.routeNeighbors source request.direction do
        unless seen[target.toNat]! do
          if nodes.size == request.nodeBudget then
            truncated := true
            break
          seen := seen.set! target.toNat true
          predecessors := predecessors.set! target.toNat
            (some { parent := source, edgeKind })
          nodes := nodes.push (target, nextDepth)
          discovered := discovered.push target
    let names := discovered.map fun id => (index.locatedAt! id).name
    let batch ← unsafe scoreCandidates env index wantedType names
    scores := scores.insertMany batch
    let ranked := (discovered.filterMap fun id => do
        let name := (index.locatedAt! id).name
        let signatureMatch ← batch.find? name
        return { id, name, distance := nextDepth, signatureMatch : ScoredEndpoint })
      |>.qsort ScoredEndpoint.betterThan
    frontier := (ranked.take request.beamWidth).map (·.id)
    depth := nextDepth
  return ({ anchor, nodes, predecessors, truncated }, scores)

private unsafe def describeNames (sourcePath : SearchPath) (env : Environment)
    (index : Index) (names : Array Name) : IO (NameMap Declaration) := do
  let mut declarations : NameMap Declaration := {}
  for (moduleName, names) in groupNamesByModule index.moduleOf? names do
    let (batch, _) ← unsafe prettyPrintModuleIO
      sourcePath env moduleName names index.moduleOf?
    declarations := declarations.insertMany batch
  return declarations

private def routeSteps (index : Index)
    (path : Array (UInt32 × Option EdgeKind)) : Array RouteStep :=
  path.map fun (id, edgeKind?) => {
    declaration := (index.locatedAt! id).name.toString
    edgeKind?
  }

private unsafe def exactRouteResult (sourcePath : SearchPath) (env : Environment)
    (index : Index) (anchorName : Name) (anchor target : UInt32)
    (wantedType : Expr) (request : RouteRequest) : IO RouteResult := do
  let shortest := index.shortestRoute anchor target request.direction
    request.maxDepth request.nodeBudget
  let results ← match shortest.path? with
    | none => pure #[]
    | some path => do
      let endpointName := (index.locatedAt! target).name
      let scores ← unsafe scoreCandidates env index wantedType #[endpointName]
      let some signatureMatch := scores.find? endpointName |
        throw <| IO.userError s!"could not score route endpoint '{endpointName}'"
      let names := path.foldl (init := ({} : NameHashSet)) fun names (id, _) =>
        names.insert (index.locatedAt! id).name
      let declarations ← unsafe describeNames sourcePath env index names.toArray
      let some endpoint := declarations.find? endpointName |
        throw <| IO.userError s!"could not describe route endpoint '{endpointName}'"
      pure #[{
        endpoint
        path := routeSteps index path
        signatureMatch
        distance := path.size - 1
      }]
  return {
    anchor := anchorName.toString
    wanted := request.wanted
    direction := request.direction
    visited := shortest.visited
    truncated := shortest.truncated
    results
  }

private unsafe def signatureRouteResult (sourcePath : SearchPath) (env : Environment)
    (index : Index) (anchorName : Name) (anchor : UInt32)
    (wantedType : Expr) (request : RouteRequest) : IO RouteResult := do
  let (reachable, scores) ← unsafe beamReachable env index anchor wantedType request
  let endpoints := reachable.nodes.extract 1 reachable.nodes.size
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
    return {
      endpoint := declaration
      path := routeSteps index (reachable.pathTo endpoint.id)
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

private unsafe def runWantedRoute (sourcePath : SearchPath) (env : Environment)
    (index : Index) (request : RouteRequest) (anchorName : Name) (anchorId : UInt32)
    (wanted : WantedTarget) : IO RouteResult :=
  match wanted.declaration? with
  | some target =>
    exactRouteResult sourcePath env index anchorName anchorId target wanted.type request
  | none =>
    signatureRouteResult sourcePath env index anchorName anchorId wanted.type request

/-- Run a route query against an already prepared project environment and index. -/
unsafe def routeWith (sourcePath : SearchPath) (env : Environment) (index : Index)
    (request : RouteRequest) : IO RouteResult := do
  let request ← normalizeRequest request
  let (anchorName, anchorId) ← resolveAnchor index request.anchor
  let run := fun env wanted =>
    runWantedRoute sourcePath env index request anchorName anchorId wanted
  unsafe withWantedTarget env index request.wanted run

/-- Find bounded declaration routes whose endpoints best match a Lean type or quoted declaration. -/
unsafe def routeFor (roots : Array Name) (request : RouteRequest) : IO RouteResult := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.materializeIndex roots
  let env ← importEnvironment roots
  unsafe routeWith sourcePath env index request

end LeanReach
