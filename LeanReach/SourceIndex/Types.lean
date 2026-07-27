import Lean.Data.NameMap
import Lean.Server.References

namespace LeanReach.SourceIndex

open Lean

/-- Dense identifier used by the persisted adjacency tables. -/
abbrev DeclId := Nat

/-- Source-visible declaration metadata recovered from `.ilean`. -/
structure Declaration where
  name : Name
  lowerName : String
  module : Name
  range : Lsp.Range
  deriving Inhabited

/-- Compressed sparse rows for one direction of the direct dependency graph. -/
structure Adjacency where
  offsets : Array Nat := #[0]
  edges : Array DeclId := #[]

@[inline] def Adjacency.neighbors (adjacency : Adjacency) (declaration : DeclId) :
    Subarray DeclId :=
  adjacency.edges.toSubarray adjacency.offsets[declaration]!
    adjacency.offsets[declaration + 1]!

/--
A compact source index over direct source references. Names are assigned dense identifiers so both
dependency directions can share compact arrays without storing a transitive closure.
-/
structure Index where
  declarations : Array Declaration := #[]
  nameToId : NameMap DeclId := {}
  upstream : Adjacency := {}
  downstream : Adjacency := {}

def Index.declarationCount (index : Index) : Nat :=
  index.declarations.size

def Index.relationCount (index : Index) : Nat :=
  index.downstream.edges.size

@[inline] def Index.findId? (index : Index) (name : Name) : Option DeclId :=
  index.nameToId.find? name

@[inline] def Index.find? (index : Index) (name : Name) : Option Declaration := do
  index.declarations[(← index.findId? name)]?

end LeanReach.SourceIndex
