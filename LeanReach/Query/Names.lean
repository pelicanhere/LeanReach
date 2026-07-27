import LeanReach.Query.Context

namespace LeanReach.Query

open Lean

abbrev ScoredName := Nat × Name

/--
A lossy 64-bit filter over consecutive lowercase character triples. Substring search uses it only
to reject impossible candidates; hash collisions are resolved by `nameScore`.
-/
def trigramFilter? (text : String) : Option UInt64 := Id.run do
  let mut first? := none
  let mut second? := none
  let mut filter := 0
  let mut found := false
  for char in text do
    match first?, second? with
    | none, _ =>
      first? := some char
    | some _, none =>
      second? := some char
    | some first, some second =>
      let hash := mixHash (hash first) (mixHash (hash second) (hash char))
      filter := filter ||| ((1 : UInt64) <<< (hash % 64))
      found := true
      first? := some second
      second? := some char
  return if found then some filter else none

def nameScore (query : String) : Name → String → Option Nat :=
  let queryName := query.toName
  let queryLower := query.toLower
  let suffixLower := "." ++ queryLower
  fun name candidateLower =>
    if name == queryName then
      some 0
    else if queryName.isSuffixOf name then
      some 1
    else if candidateLower == queryLower then
      some 2
    else if candidateLower.endsWith suffixLower then
      some 3
    else if candidateLower.contains queryLower then
      some 4
    else
      none

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
