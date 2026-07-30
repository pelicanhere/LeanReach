import LeanReach.Search.Name
import LeanReach.Search.TopK
import LeanReach.Search.Types

namespace LeanReach

open Lean

universe u

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
  ((NameSearch.leaf (privateToUserName name)).toLower.splitOn "_").filter (·.length ≥ 3)

private def tokenSimilarity (left right : List String) : Float :=
  diceScore left.length right.length (left.countP right.contains)

private def localityScore (source : LocatedName) (sourceNameParts sourceModuleParts : List Name)
    (sourceParts : List String) (candidate : LocatedName) : Float :=
  (if source.moduleName == candidate.moduleName then 3.0 else 0.0) +
    3.0 * prefixSimilarity sourceNameParts (privateToUserName candidate.name).components +
    2.0 * prefixSimilarity sourceModuleParts candidate.moduleName.components +
    4.0 * tokenSimilarity sourceParts (significantParts candidate.name)

private def rankPositions (size limit : Nat) (score : Nat → Float)
    (name : Nat → Name) : Array Nat :=
  let better := fun (scoreA, a) (scoreB, b) =>
    if scoreA != scoreB then scoreA > scoreB else Name.lt (name a) (name b)
  (TopK.select size limit (fun id => (score id, id)) better).map (·.2)

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
  let sourceNameParts := (privateToUserName source.name).components
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
