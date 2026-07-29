import Lean.Data.Name

namespace LeanReach.NameSearch

open Lean

def leaf : Name → String
  | .str _ value => value
  | .num _ value => toString value
  | .anonymous => ""

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

def bucket? (query : String) (name : Name) : Option Nat :=
  let candidate := name.toString.toLower
  if candidate == query then some 0
  else if candidate.endsWith ("." ++ query) then some 1
  else if candidate.contains query then some 2
  else none

end LeanReach.NameSearch
