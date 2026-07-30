import LeanReach.Search.Name

namespace LeanReach.NameSearch

open Lean

universe u v

def trigrams (value : String) : Array String := Id.run do
  let mut result := #[]
  let length := value.length
  for offset in [0:length] do
    if length < offset + 3 then break
    result := result.push ((value.drop offset).take 3).copy
  return result

def exact (query : String) (name : Name) : Bool :=
  name.toString.toLower == query

def leafMatches (query : String) (name : Name) : Bool :=
  (leaf name).toLower == query

private def bucket? (query : String) (name : Name) : Option Nat :=
  let candidate := name.toString.toLower
  if candidate == query then some 0
  else if candidate.endsWith ("." ++ query) then some 1
  else if candidate.contains query then some 2
  else none

def buckets {α : Type u} {β : Type v} (query : String)
    (items : Array α) (project : α → Option β) (nameOf : β → Name)
    (limit : Nat) : Array (Array β) := Id.run do
  let query := query.toLower
  let mut buckets : Array (Array β) := #[#[], #[], #[]]
  for item in items do
    let some item := project item | continue
    let name := nameOf item
    if let some bucket := bucket? query name then
      if buckets[bucket]!.size < limit then
        buckets := buckets.modify bucket (·.push item)
  return buckets

end LeanReach.NameSearch
