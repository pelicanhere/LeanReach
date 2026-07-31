module

public import Lean.Data.Name
public import Lean.PrivateName

@[expose] public section

namespace LeanReach.NameSearch

open Lean

def leaf? : Name → Option String
  | .str _ value => some value
  | _ => none

def exactMatch (query candidate : Name) : Bool :=
  candidate == query ||
    (!isPrivateName query && privateToUserName candidate == query)

def findSorted? (size : Nat) (nameAt : Nat → Name) (target : Name) : Option Nat := Id.run do
  let mut lo := 0
  let mut hi := size
  while lo < hi do
    let mid := (lo + hi) / 2
    let candidate := nameAt mid
    if candidate == target then return some mid
    if Name.lt candidate target then lo := mid + 1 else hi := mid
  return none

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
