import LeanReach.Search.Match
import LeanReach.Search.TopK
import LeanReach.Search.Types

namespace LeanReach

open Lean

universe u

namespace Rank

structure Features where
  name : Name
  nameDepth : Nat
  moduleDepth : Nat
  tokens : Array String
  deriving Inhabited

private def commonPrefixLength (left right : Name)
    (leftDepth rightDepth : Nat) : Nat := Id.run do
  let mut left := left
  let mut right := right
  let mut leftDepth := leftDepth
  let mut rightDepth := rightDepth
  while leftDepth > rightDepth do
    left := left.getPrefix
    leftDepth := leftDepth - 1
  while rightDepth > leftDepth do
    right := right.getPrefix
    rightDepth := rightDepth - 1
  while left != right do
    left := left.getPrefix
    right := right.getPrefix
    leftDepth := leftDepth - 1
  return leftDepth

private def diceScore (left right shared : Nat) : Float :=
  let total := left + right
  if total == 0 then 0.0 else 2.0 * shared.toFloat / total.toFloat

private def prefixSimilarity (left right : Name)
    (leftDepth rightDepth : Nat) : Float :=
  diceScore leftDepth rightDepth
    (commonPrefixLength left right leftDepth rightDepth)

private def significantParts (name : Name) : Array String :=
  (((NameSearch.leaf? (privateToUserName name)).getD "").toLower.splitOn "_")
    |>.filter (·.length ≥ 3)
    |>.eraseDups
    |>.toArray

def features (declaration : LocatedName) : Features :=
  let name := privateToUserName declaration.name
  {
    name
    nameDepth := name.getNumParts
    moduleDepth := declaration.moduleName.getNumParts
    tokens := significantParts declaration.name
  }

private def tokenSimilarity (left right : Array String) : Float :=
  diceScore left.size right.size (left.countP right.contains)

private def affinity (source : LocatedName) (sourceFeatures : Features)
    (candidate : LocatedName) (candidateFeatures : Features) : Float :=
  ((if source.moduleName == candidate.moduleName then 3.0 else 0.0) +
    3.0 * prefixSimilarity sourceFeatures.name candidateFeatures.name
      sourceFeatures.nameDepth candidateFeatures.nameDepth +
    2.0 * prefixSimilarity source.moduleName candidate.moduleName
      sourceFeatures.moduleDepth candidateFeatures.moduleDepth +
    4.0 * tokenSimilarity sourceFeatures.tokens candidateFeatures.tokens) / 8.0

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

def selectWith {α : Type u} [Inhabited α] (source : LocatedName)
    (sourceFeatures : Features) (candidates : Array α)
    (located : α → LocatedName) (candidateFeatures : α → Features)
    (candidatePrior : α → Float) (limit : Nat) : Array α :=
  let candidateAt position := candidates[position]!
  let positions := rankPositions candidates.size limit
    (fun position =>
      let candidate := candidateAt position
      candidatePrior candidate *
        (1.0 + affinity source sourceFeatures
          (located candidate) (candidateFeatures candidate)))
    (fun position => (located (candidateAt position)).name)
  positions.map candidateAt

def select {α : Type u} [Inhabited α] (source : LocatedName) (candidates : Array α)
    (located : α → LocatedName) (candidatePrior : α → Float)
    (limit : Nat) : Array α :=
  selectWith source (features source) candidates located
    (features ∘ located) candidatePrior limit

end Rank
end LeanReach
