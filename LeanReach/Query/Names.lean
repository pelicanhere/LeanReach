import LeanReach.Query.Context

namespace LeanReach.Query

open Lean

abbrev ScoredName := Nat × Name

def nameScore (query : String) : Name → Option Nat :=
  let queryLower := query.toLower
  let suffix := "." ++ query
  let suffixLower := "." ++ queryLower
  fun name =>
    let candidate := nameString name
    if candidate == query then
      some 0
    else if candidate.endsWith suffix then
      some 1
    else
      let candidateLower := candidate.toLower
      if candidateLower == queryLower then
        some 2
      else if candidateLower.endsWith suffixLower then
        some 3
      else if candidateLower.contains queryLower then
        some 4
      else
        none

def sortScoredNames (hits : Array ScoredName) : Array ScoredName :=
  hits.qsort fun left right =>
    left.1 < right.1 || (left.1 == right.1 && Name.quickLt left.2 right.2)

def resolveScoredName (query : String) (hits : Array ScoredName) :
    Except (QueryError Name) Name := do
  let suggestions := (hits.take 10).map (·.2)
  let some best := hits[0]? | throw {
    error := s!"unknown declaration '{query}'"
    candidates := #[]
  }
  let bestMatches := hits.takeWhile (·.1 == best.1)
  if best.1 ≤ 3 && bestMatches.size == 1 then
    return best.2
  if best.1 ≤ 3 then
    throw {
      error := s!"ambiguous declaration '{query}'"
      candidates := suggestions
    }
  throw {
    error := s!"unknown declaration '{query}'"
    candidates := suggestions
  }

end LeanReach.Query
