import Lean.Data.Name
import LeanReach.Protocol

namespace LeanReach.Query

open Lean

abbrev RawRelation := Relation Name Name

def visibleName (includeInternal : Bool) (name : Name) : Bool :=
  includeInternal || !name.isInternalDetail

def nameString (name : Name) : String :=
  name.toString (escape := false)

def rawRelationLt (left right : RawRelation) : Bool :=
  left.distance < right.distance ||
    (left.distance == right.distance &&
      Name.quickLt left.declaration right.declaration)

end LeanReach.Query
