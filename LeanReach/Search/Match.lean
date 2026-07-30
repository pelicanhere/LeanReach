module

public import Lean.Data.Name
public import Lean.PrivateName

@[expose] public section

namespace LeanReach.NameSearch

open Lean

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

end LeanReach.NameSearch
