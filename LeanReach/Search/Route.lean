import LeanReach.Search.Index

namespace LeanReach

open Lean

inductive RouteDirection where
  | dependencies
  | consumers
  deriving Inhabited, BEq, Repr

def RouteDirection.opposite : RouteDirection → RouteDirection
  | .dependencies => .consumers
  | .consumers => .dependencies

structure RoutePredecessor where
  parent : UInt32
  edgeKind : EdgeKind
  deriving Inhabited

structure Reachability where
  anchor : UInt32
  nodes : Array (UInt32 × Nat)
  predecessors : Array (Option RoutePredecessor)
  truncated : Bool
  deriving Inhabited

def Index.routeNeighbors (index : Index) (source : UInt32)
    (direction : RouteDirection) : Array (UInt32 × EdgeKind) :=
  let dependencies := index.directDependencies source (direction == .dependencies)
  ((dependencies.typeDeps.map fun id => (id, EdgeKind.typeDependency)) ++
      (dependencies.bodyDeps.map fun id => (id, EdgeKind.bodyDependency)))
    |>.qsort fun left right =>
      Name.lt (index.locatedAt! left.1).name (index.locatedAt! right.1).name

def Reachability.pathTo (reachability : Reachability)
    (endpoint : UInt32) : Array (UInt32 × Option EdgeKind) := Id.run do
  let mut path := #[]
  let mut current := endpoint
  let mut remaining := reachability.nodes.size
  while current != reachability.anchor && remaining > 0 do
    let some predecessor := reachability.predecessors[current.toNat]! | return #[]
    path := path.push (current, some predecessor.edgeKind)
    current := predecessor.parent
    remaining := remaining - 1
  if current != reachability.anchor then return #[]
  return (path.push (reachability.anchor, none)).reverse

private structure RouteSuccessor where
  child : UInt32
  edgeKind : EdgeKind

private structure RouteMeeting where
  id : UInt32
  distance : Nat

private def RouteMeeting.choose (index : Index) (current : Option RouteMeeting)
    (id : UInt32) (distance : Nat) : Option RouteMeeting :=
  match current with
  | none => some { id, distance }
  | some best =>
    if distance < best.distance || distance == best.distance &&
        Name.lt (index.locatedAt! id).name (index.locatedAt! best.id).name then
      some { id, distance }
    else
      some best

structure ShortestRoute where
  path? : Option (Array (UInt32 × Option EdgeKind))
  visited : Nat
  truncated : Bool

private def reconstructRoute (anchor target meeting : UInt32)
    (predecessors : Array (Option RoutePredecessor))
    (successors : Array (Option RouteSuccessor))
    (nodeCount : Nat) : Array (UInt32 × Option EdgeKind) := Id.run do
  let mut beforeMeeting := #[]
  let mut current := meeting
  let mut remaining := nodeCount
  while current != anchor && remaining > 0 do
    let some predecessor := predecessors[current.toNat]! | return #[]
    beforeMeeting := beforeMeeting.push (current, some predecessor.edgeKind)
    current := predecessor.parent
    remaining := remaining - 1
  if current != anchor then return #[]
  let mut path := (beforeMeeting.push (anchor, none)).reverse
  current := meeting
  remaining := nodeCount
  while current != target && remaining > 0 do
    let some successor := successors[current.toNat]! | return #[]
    path := path.push (successor.child, some successor.edgeKind)
    current := successor.child
    remaining := remaining - 1
  if current != target then return #[]
  return path

/-- Find a shortest directed route by expanding breadth-first layers from both endpoints. -/
def Index.shortestRoute (index : Index) (anchor target : UInt32)
    (direction : RouteDirection) (maxDepth nodeBudget : Nat) : ShortestRoute := Id.run do
  if nodeBudget == 0 then return { path? := none, visited := 0, truncated := true }
  if anchor == target then
    return { path? := some #[(anchor, none)], visited := 1, truncated := false }
  if nodeBudget == 1 then return { path? := none, visited := 1, truncated := true }
  let mut forwardDistance : Array (Option Nat) := Array.replicate index.size none
  let mut backwardDistance : Array (Option Nat) := Array.replicate index.size none
  let mut predecessors : Array (Option RoutePredecessor) := Array.replicate index.size none
  let mut successors : Array (Option RouteSuccessor) := Array.replicate index.size none
  let mut visitedAny := Array.replicate index.size false
  forwardDistance := forwardDistance.set! anchor.toNat (some 0)
  backwardDistance := backwardDistance.set! target.toNat (some 0)
  visitedAny := visitedAny.set! anchor.toNat true
  visitedAny := visitedAny.set! target.toNat true
  let mut visited := 2
  let mut forwardFrontier := #[anchor]
  let mut backwardFrontier := #[target]
  let mut forwardDepth := 0
  let mut backwardDepth := 0
  let mut best? : Option RouteMeeting := none
  let mut truncated := false
  while !forwardFrontier.isEmpty && !backwardFrontier.isEmpty &&
      forwardDepth + backwardDepth < maxDepth && !truncated do
    if forwardFrontier.size <= backwardFrontier.size then
      let nextDepth := forwardDepth + 1
      let mut next := #[]
      for source in forwardFrontier do
        if truncated then break
        for (neighbor, edgeKind) in index.routeNeighbors source direction do
          if forwardDistance[neighbor.toNat]!.isNone then
            let alreadyVisited := visitedAny[neighbor.toNat]!
            if !alreadyVisited && visited == nodeBudget then
              truncated := true
              break
            forwardDistance := forwardDistance.set! neighbor.toNat (some nextDepth)
            predecessors := predecessors.set! neighbor.toNat
              (some { parent := source, edgeKind })
            next := next.push neighbor
            unless alreadyVisited do
              visitedAny := visitedAny.set! neighbor.toNat true
              visited := visited + 1
            if let some distance := backwardDistance[neighbor.toNat]! then
              let total := nextDepth + distance
              if total <= maxDepth then
                best? := RouteMeeting.choose index best? neighbor total
      forwardFrontier := next
      forwardDepth := nextDepth
    else
      let nextDepth := backwardDepth + 1
      let mut next := #[]
      for source in backwardFrontier do
        if truncated then break
        for (neighbor, edgeKind) in index.routeNeighbors source direction.opposite do
          if backwardDistance[neighbor.toNat]!.isNone then
            let alreadyVisited := visitedAny[neighbor.toNat]!
            if !alreadyVisited && visited == nodeBudget then
              truncated := true
              break
            backwardDistance := backwardDistance.set! neighbor.toNat (some nextDepth)
            successors := successors.set! neighbor.toNat
              (some { child := source, edgeKind })
            next := next.push neighbor
            unless alreadyVisited do
              visitedAny := visitedAny.set! neighbor.toNat true
              visited := visited + 1
            if let some distance := forwardDistance[neighbor.toNat]! then
              let total := nextDepth + distance
              if total <= maxDepth then
                best? := RouteMeeting.choose index best? neighbor total
      backwardFrontier := next
      backwardDepth := nextDepth
    if let some best := best? then
      if forwardDepth + backwardDepth >= best.distance then break
  return {
    path? := best?.map fun best => reconstructRoute anchor target best.id
      predecessors successors index.size
    visited
    truncated
  }

end LeanReach
