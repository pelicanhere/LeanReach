import LeanReach.Search.Match
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

private def affinity (source : LocatedName) (sourceName sourceModule : List Name)
    (sourceParts : List String) (candidate : LocatedName) : Float :=
  ((if source.moduleName == candidate.moduleName then 3.0 else 0.0) +
    3.0 * prefixSimilarity sourceName (privateToUserName candidate.name).components +
    2.0 * prefixSimilarity sourceModule candidate.moduleName.components +
    4.0 * tokenSimilarity sourceParts (significantParts candidate.name)) / 8.0

private def rankPositions (size limit : Nat) (score : Nat → Float)
    (name : Nat → Name) : Array Nat :=
  let better := fun (scoreA, a) (scoreB, b) =>
    if scoreA != scoreB then scoreA > scoreB else Name.lt (name a) (name b)
  (TopK.select size limit (fun id => (score id, id)) better).map (·.2)

def prior (total reverseCount forwardCount : Nat) (upstream : Bool) : Float :=
  let users := reverseCount.toFloat
  let dependencies := forwardCount.toFloat
  let specificity :=
    Float.log (1.0 + (total.toFloat - users + 0.5) / (users + 0.5))
  let confidence := users / (users + 0.5)
  let substance := 4.0 * dependencies / (dependencies + users + 8.0)
  (if upstream then specificity * confidence else Float.log (1.0 + users)) +
    substance

def priors (forward reverse : Array (Array UInt32))
    (upstream : Bool) : Array Float :=
  forward.mapIdx fun id dependencies =>
    prior forward.size reverse[id]!.size dependencies.size upstream

def select {α : Type u} [Inhabited α] (source : LocatedName) (candidates : Array α)
    (located : α → LocatedName) (candidatePrior : α → Float)
    (limit : Nat) : Array α :=
  let sourceName := (privateToUserName source.name).components
  let sourceModule := source.moduleName.components
  let sourceParts := significantParts source.name
  let candidateAt position := candidates[position]!
  let positions := rankPositions candidates.size limit
    (fun position =>
      let candidate := candidateAt position
      candidatePrior candidate *
        (1.0 + affinity source sourceName sourceModule sourceParts (located candidate)))
    (fun position => (located (candidateAt position)).name)
  positions.map candidateAt

end Rank
end LeanReach
