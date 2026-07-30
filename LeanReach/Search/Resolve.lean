import Lean.Data.NameMap.Basic
import LeanReach.Search.Match
import LeanReach.Search.Types

namespace LeanReach.NameResolve

open Lean

universe u v

def leafMatches (query : String) (name : Name) : Bool :=
  (NameSearch.leaf (privateToUserName name)).toLower == query

private def bucket? (query suffix : String) (name : Name) : Option Nat :=
  let candidate := NameSearch.normalizedName name
  if candidate == query then some 0
  else if candidate.endsWith suffix then some 1
  else if candidate.contains query then some 2
  else none

def buckets {α : Type u} {β : Type v} (queryLower : String)
    (size : Nat) (itemAt : Nat → α) (project : α → Option β) (nameOf : β → Name)
    (limit : Nat) : Array (Array β) := Id.run do
  let mut buckets : Array (Array β) := #[#[], #[], #[]]
  let suffix := "." ++ queryLower
  for position in [0:size] do
    let some item := project (itemAt position) | continue
    if let some bucket := bucket? queryLower suffix (nameOf item) then
      if buckets[bucket]!.size < limit then
        buckets := buckets.modify bucket (·.push item)
  return buckets

def collect {α : Type u} {β : Type v} (queryLower : String)
    (size : Nat) (itemAt : Nat → α) (project : α → Option β) (nameOf : β → Name)
    (limit : Nat) : Array β :=
  (buckets queryLower size itemAt project nameOf limit).flatten.take limit

def bestBucket {α : Type u} (buckets : Array (Array α)) : Array α :=
  buckets.find? (not ∘ Array.isEmpty) |>.getD #[]

def mergeBuckets (queryLower : String) (limit : Nat)
    (left right : Array LocatedName) : Array (Array LocatedName) := Id.run do
  let mut seen : NameHashSet := {}
  let mut candidates := #[]
  for target in left ++ right do
    unless seen.contains target.name do
      seen := seen.insert target.name
      candidates := candidates.push target
  candidates := candidates.qsort fun a b => Name.lt a.name b.name
  return buckets queryLower candidates.size
    (fun id => candidates[id]!) some (·.name) limit

end LeanReach.NameResolve
