import LeanReach.Query

namespace LeanReach

def maxDepth : Nat := 8

def maxLimit : Nat := 1000

def parseDependencyMode (label value : String) : Except String DependencyMode :=
  match value with
  | "source" => .ok .source
  | "kernel" => .ok .kernel
  | _ => .error s!"{label} expects source or kernel; got '{value}'"

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

def parseDepth (label value : String) : Except String Nat := do
  let depth ← match value.toNat? with
    | some depth => pure depth
    | none => throw s!"{label} expects a natural number, got '{value}'"
  validateDepth label depth

def parseLimit (label value : String) : Except String Nat := do
  let limit ← match value.toNat? with
    | some limit => pure limit
    | none => throw s!"{label} expects a natural number, got '{value}'"
  validateLimit label limit

end LeanReach
