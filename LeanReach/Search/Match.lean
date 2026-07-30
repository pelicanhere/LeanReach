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
  let mut start := value.startPos
  let mut stop := start
  for _ in [0:3] do
    let some next := stop.next? | return result
    stop := next
  while true do
    result := result.push (value.extract start stop)
    let some nextStop := stop.next? | break
    start := start.next!
    stop := nextStop
  return result

def rarestTrigram? (grams : Array String)
    (count? : String → Option Nat) : Option String := Id.run do
  let mut selected : Option (String × Nat) := none
  for gram in grams do
    let count := (count? gram).getD 0
    if selected.all (count < ·.2) then selected := some (gram, count)
  return selected.bind fun (gram, count) => if count == 0 then none else some gram

def leafMatches (query : String) (name : Name) : Bool :=
  (leaf (privateToUserName name)).toLower == query

private def bucket? (query suffix : String) (name : Name) : Option Nat :=
  let candidate := normalizedName name
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
    let name := nameOf item
    if let some bucket := bucket? queryLower suffix name then
      if buckets[bucket]!.size < limit then
        buckets := buckets.modify bucket (·.push item)
  return buckets

def collect {α : Type u} {β : Type v} (queryLower : String)
    (size : Nat) (itemAt : Nat → α) (project : α → Option β) (nameOf : β → Name)
    (limit : Nat) : Array β :=
  (buckets queryLower size itemAt project nameOf limit).flatten.take limit

def bestBucket {α : Type u} (buckets : Array (Array α)) : Array α :=
  buckets.find? (not ∘ Array.isEmpty) |>.getD #[]

end LeanReach.NameSearch
