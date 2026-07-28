import LeanReach.Index

namespace LeanReach

open Lean

abbrev RankedName := Float × Nat × Name

private def expansionWidth := 16
private def expansionBudget := 256

private def comesBefore : RankedName → RankedName → Bool
  | (score₁, distance₁, name₁), (score₂, distance₂, name₂) =>
    score₁ > score₂ ||
      score₁ == score₂ && (distance₁ < distance₂ ||
        distance₁ == distance₂ && Name.lt name₁ name₂)

def Index.idf (index : Index) (name : Name) : Float :=
  let n := index.declarationCount.toFloat
  let df := (index.documentFrequency name).toFloat
  Float.log (1.0 + (n - df + 0.5) / (df + 0.5))

private def Index.rank (index : Index) (distance : Nat) (names : Array Name) :
    Array RankedName := Id.run do
  let weight := Float.pow 0.5 (distance - 1).toFloat
  let mut ranked := #[]
  for name in names do
    ranked := ranked.push (index.idf name * weight, distance, name)
  return ranked.qsort comesBefore

private def frontier (ranked : Array RankedName) : Array Name :=
  (ranked.take expansionWidth).map fun (_, _, name) => name

private def Index.expand (index : Index) (current : Array Name)
    (seen : NameHashSet) (budget : Nat) : Array Name × NameHashSet × Nat := Id.run do
  let mut next : NameSet := {}
  let mut seen := seen
  let mut remaining := budget
  for name in current do
    for dependency in index.upstream name do
      if remaining == 0 then return (next.toArray, seen, remaining)
      remaining := remaining - 1
      unless seen.contains dependency do
        seen := seen.insert dependency
        next := next.insert dependency
  return (next.toArray, seen, remaining)

/-- Rank a bounded, demand-driven upstream neighborhood by symbol rarity. -/
def Index.context (index : Index) (target : Name) (depth limit : Nat) :
    Array RankedName := Id.run do
  if depth == 0 || limit == 0 then return #[]
  let direct := index.rank 1 (index.upstream target)
  if depth == 1 || direct.isEmpty then return direct.take limit
  let mut ranked := direct
  let mut current := frontier direct
  let mut seen : NameHashSet := ({} : NameHashSet).insert target
  for (_, _, name) in direct do
    seen := seen.insert name
  let mut budget := expansionBudget
  for distance in [2:depth + 1] do
    let (next, seen', budget') := index.expand current seen budget
    seen := seen'
    budget := budget'
    let layer := index.rank distance next
    ranked := ranked ++ layer
    current := frontier layer
    if current.isEmpty || budget == 0 then break
  return (ranked.qsort comesBefore).take limit

def Index.contextNames (index : Index) (query : String) (depth limit : Nat) :
    Except String (Name × Array RankedName) := do
  let target ← index.resolve query
  return (target, index.context target depth limit)

end LeanReach
