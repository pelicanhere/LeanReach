import Lean.Data.Json
import Lean.PrivateName

namespace LeanReach

structure Declaration where
  name : String
  signature : String
  moduleName : String
  file : Option String
  line : Nat
  column : Nat

instance : Lean.ToJson Declaration where
  toJson d :=
    let queryName := d.name
    let name := (Lean.privateToUserName queryName.toName).toString
    Lean.Json.mkObj [
    ("queryName", Lean.toJson queryName), ("name", Lean.toJson name),
    ("signature", Lean.toJson d.signature),
    ("source", Lean.Json.mkObj [
      ("moduleName", Lean.toJson d.moduleName), ("file", Lean.toJson d.file),
      ("line", Lean.toJson d.line), ("column", Lean.toJson d.column)
    ])
  ]

end LeanReach
