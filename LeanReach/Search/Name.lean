import Lean.Data.Name
import Lean.PrivateName

namespace LeanReach.NameSearch

open Lean

def leaf (name : Name) : String :=
  name.getString!

end LeanReach.NameSearch
