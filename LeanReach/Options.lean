import LeanReach.Protocol

namespace LeanReach

private def maxDepth : Nat := 8

private def maxLimit : Nat := 1000

def parseDirection (label value : String) : Except String Direction :=
  match value with
  | "both" => .ok .both
  | "upstream" | "up" => .ok .upstream
  | "downstream" | "down" => .ok .downstream
  | _ => .error s!"{label} expects both, upstream, or downstream; got '{value}'"

def validateDepth (label : String) (depth : Nat) : Except String Nat :=
  if depth > maxDepth then
    .error s!"{label} must be at most {maxDepth}; downstream work is linear per layer"
  else
    .ok depth

def validateLimit (label : String) (limit : Nat) : Except String Nat :=
  if limit == 0 || limit > maxLimit then
    .error s!"{label} must be between 1 and {maxLimit}"
  else
    .ok limit

private def parseNat (label value : String) : Except String Nat :=
  match value.toNat? with
  | some value => .ok value
  | none => .error s!"{label} expects a natural number, got '{value}'"

def parseDepth (label value : String) : Except String Nat :=
  parseNat label value >>= validateDepth label

def parseLimit (label value : String) : Except String Nat :=
  parseNat label value >>= validateLimit label

end LeanReach
