import Lean.Data.Name
import Lean.PrivateName

namespace LeanReach.NameSearch

open Lean

universe u v

def leaf (name : Name) : String :=
  name.getString!

def normalizedName (name : Name) : String :=
  (privateToUserName name).toString.toLower

def trigrams (value : String) : Array String := Id.run do
  let mut result := #[]
  let length := value.length
  for offset in [0:length] do
    if length < offset + 3 then break
    result := result.push ((value.drop offset).take 3).copy
  return result

def rarestTrigram? (grams : Array String)
    (count? : String → Option Nat) : Option String := Id.run do
  let mut selected : Option (String × Nat) := none
  for gram in grams do
    let count := (count? gram).getD 0
    if selected.all (count < ·.2) then selected := some (gram, count)
  return selected.bind fun (gram, count) => if count == 0 then none else some gram

def exact (query : String) (name : Name) : Bool :=
  normalizedName name == query

def leafMatches (query : String) (name : Name) : Bool :=
  (leaf (privateToUserName name)).toLower == query

private def bucket? (query : String) (name : Name) : Option Nat :=
  let candidate := normalizedName name
  if candidate == query then some 0
  else if candidate.endsWith ("." ++ query) then some 1
  else if candidate.contains query then some 2
  else none

def isMatch (queryLower : String) (name : Name) : Bool :=
  (bucket? queryLower name).isSome

def buckets {α : Type u} {β : Type v} (queryLower : String)
    (items : Array α) (project : α → Option β) (nameOf : β → Name)
    (limit : Nat) : Array (Array β) := Id.run do
  let mut buckets : Array (Array β) := #[#[], #[], #[]]
  for item in items do
    let some item := project item | continue
    let name := nameOf item
    if let some bucket := bucket? queryLower name then
      if buckets[bucket]!.size < limit then
        buckets := buckets.modify bucket (·.push item)
  return buckets

def collect {α : Type u} {β : Type v} (queryLower : String)
    (items : Array α) (project : α → Option β) (nameOf : β → Name)
    (limit : Nat) : Array β :=
  (buckets queryLower items project nameOf limit).flatten.take limit

end LeanReach.NameSearch
