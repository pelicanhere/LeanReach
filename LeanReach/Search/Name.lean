import Lean.Data.Name

namespace LeanReach.NameSearch

open Lean

def leaf : Name → String
  | .str _ value => value
  | .num _ value => toString value
  | .anonymous => ""

end LeanReach.NameSearch
