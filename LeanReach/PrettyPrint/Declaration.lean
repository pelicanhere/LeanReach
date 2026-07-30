import Lean

namespace LeanReach

structure Declaration where
  name : String
  signature : String
  moduleName : String
  file : Option String
  line : Nat
  column : Nat

instance : Lean.ToJson Declaration where
  toJson d := Lean.Json.mkObj [
    ("name", Lean.toJson d.name), ("signature", Lean.toJson d.signature),
    ("source", Lean.Json.mkObj [
      ("moduleName", Lean.toJson d.moduleName), ("file", Lean.toJson d.file),
      ("line", Lean.toJson d.line), ("column", Lean.toJson d.column)
    ])
  ]

end LeanReach
