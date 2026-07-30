import Lean.Data.Name
import LeanReach.Search.Name

namespace LeanReach

open Lean

universe u

structure LocatedName where
  name : Name
  moduleName : Name
  deriving Inhabited

namespace Rank

private def commonPrefixLength : List Name → List Name → Nat
  | a :: as, b :: bs => if a == b then commonPrefixLength as bs + 1 else 0
  | _, _ => 0

private def diceScore (left right shared : Nat) : Float :=
  let total := left + right
  if total == 0 then 0.0 else 2.0 * shared.toFloat / total.toFloat

private def prefixSimilarity (left right : List Name) : Float :=
  diceScore left.length right.length (commonPrefixLength left right)

private def significantParts (name : Name) : List String :=
  ((NameSearch.leaf name).toLower.splitOn "_").filter (·.length ≥ 3)

private def tokenSimilarity (left right : List String) : Float :=
  diceScore left.length right.length (left.countP right.contains)

private def localityScore (source : LocatedName) (sourceNameParts sourceModuleParts : List Name)
    (sourceParts : List String) (candidate : LocatedName) : Float :=
  (if source.moduleName == candidate.moduleName then 3.0 else 0.0) +
    3.0 * prefixSimilarity sourceNameParts candidate.name.components +
    2.0 * prefixSimilarity sourceModuleParts candidate.moduleName.components +
    4.0 * tokenSimilarity sourceParts (significantParts candidate.name)

private def heapifyDown {α : Type u} [Inhabited α] (lt : α → α → Bool)
    (items : Array α) : Array α := Id.run do
  let mut items := items
  let mut parent : Nat := 0
  while 2 * parent + 1 < items.size do
    let left := 2 * parent + 1
    let right := left + 1
    let child :=
      if right < items.size && lt items[left]! items[right]! then right else left
    if lt items[parent]! items[child]! then
      items := items.swapIfInBounds parent child
      parent := child
    else break
  return items

private def heapInsert {α : Type u} [Inhabited α] (lt : α → α → Bool)
    (items : Array α) (item : α) : Array α := Id.run do
  let mut items := items.push item
  let mut child := items.size - 1
  while child > 0 do
    let parent := (child - 1) / 2
    if lt items[parent]! items[child]! then
      items := items.swapIfInBounds parent child
      child := parent
    else break
  return items

private def rankPositions (size limit : Nat) (score : Nat → Float)
    (name : Nat → Name) : Array Nat := Id.run do
  if limit == 0 || size == 0 then return #[]
  if size == 1 then return #[0]
  let better := fun (scoreA, a) (scoreB, b) =>
    if scoreA != scoreB then scoreA > scoreB else Name.lt (name a) (name b)
  let best :=
    if size ≤ limit then
      (Array.range size).map fun id => (score id, id)
    else Id.run do
      let mut heap := #[]
      for id in [0:size] do
        let item := (score id, id)
        if heap.size < limit then
          heap := heapInsert better heap item
        else if let some worst := heap[0]? then
          if better item worst then
            heap := heapifyDown better (heap.set! 0 item)
      return heap
  return (best.qsort better).map (·.2)

def prior (total reverseCount forwardCount : Nat) (upstream : Bool) : Float :=
  let df := reverseCount.toFloat
  let specificity :=
    Float.log (1.0 + (total.toFloat - df + 0.5) / (df + 0.5))
  let support := df / (df + 0.5)
  let out := forwardCount.toFloat
  let substance := 4.0 * out / (out + df + 8.0)
  if upstream then specificity * support + substance
  else Float.log (1.0 + df) + substance

def priors (forward reverse : Array (Array UInt32))
    (upstream : Bool) : Array Float :=
  forward.mapIdx fun id outgoing =>
    prior forward.size reverse[id]!.size outgoing.size upstream

def select {α : Type u} [Inhabited α] (source : LocatedName) (candidates : Array α)
    (located : α → LocatedName) (candidatePrior : α → Float)
    (limit : Nat) : Array α := Id.run do
  let sourceNameParts := source.name.components
  let sourceModuleParts := source.moduleName.components
  let sourceParts := significantParts source.name
  let candidateAt position := candidates[position]!
  let positions := rankPositions candidates.size limit
    (fun position =>
      let candidate := candidateAt position
      candidatePrior candidate * (1.0 + localityScore source sourceNameParts
        sourceModuleParts sourceParts (located candidate) / 8.0))
    (fun position => (located (candidateAt position)).name)
  return positions.map candidateAt

end Rank
end LeanReach
