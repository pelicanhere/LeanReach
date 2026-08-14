import LeanReach.Search.Index

namespace LeanReach

open Lean

inductive RouteDirection where
  | dependencies
  | consumers
  deriving Inhabited, BEq, Repr

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

private def Index.routeNeighbors (index : Index) (source : UInt32)
    (direction : RouteDirection) : Array (UInt32 × EdgeKind) :=
  let dependencies := index.directDependencies source (direction == .dependencies)
  ((dependencies.typeDeps.map fun id => (id, EdgeKind.typeDependency)) ++
      (dependencies.bodyDeps.map fun id => (id, EdgeKind.bodyDependency)))
    |>.qsort fun left right =>
      Name.lt (index.locatedAt! left.1).name (index.locatedAt! right.1).name

def Index.reachable (index : Index) (anchor : UInt32) (direction : RouteDirection)
    (maxDepth nodeBudget : Nat) : Reachability := Id.run do
  let mut seen := Array.replicate index.size false
  let mut predecessors := Array.replicate index.size none
  let mut nodes := #[(anchor, 0)]
  let mut position := 0
  let mut truncated := false
  seen := seen.set! anchor.toNat true
  while position < nodes.size && !truncated do
    let (source, depth) := nodes[position]!
    position := position + 1
    if depth < maxDepth then
      for (target, edgeKind) in index.routeNeighbors source direction do
        unless seen[target.toNat]! do
          if nodes.size == nodeBudget then
            truncated := true
            break
          seen := seen.set! target.toNat true
          predecessors := predecessors.set! target.toNat (some { parent := source, edgeKind })
          nodes := nodes.push (target, depth + 1)
  return { anchor, nodes, predecessors, truncated }

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

end LeanReach
