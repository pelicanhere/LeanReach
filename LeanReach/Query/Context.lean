import Lean.CoreM
import Lean.Data.Name
import Lean.Util.Path
import LeanReach.Protocol

namespace LeanReach.Query

open Lean Lean.Core

abbrev RawRelation := Relation Name Name

/-- Query actions that share the source search path for one imported environment. -/
abbrev SessionM := ReaderT SearchPath CoreM

/-- Query actions that read one request's options. -/
abbrev RequestM := ReaderT QueryOptions SessionM

def visibleName (includeInternal : Bool) (name : Name) : Bool :=
  includeInternal || !name.isInternalDetail

def nameString (name : Name) : String :=
  name.toString (escape := false)

def rawRelationLt (left right : RawRelation) : Bool :=
  left.distance < right.distance ||
    (left.distance == right.distance &&
      Name.quickLt left.declaration right.declaration)

end LeanReach.Query
