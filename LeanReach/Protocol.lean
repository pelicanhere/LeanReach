import Lean.Data.Json

namespace LeanReach

open Lean

/-- Which side of a declaration's dependency neighborhood to inspect. -/
inductive Direction where
  | both
  | upstream
  | downstream
  deriving FromJson

namespace Direction

def includesUpstream : Direction → Bool
  | .both | .upstream => true
  | .downstream => false

def includesDownstream : Direction → Bool
  | .both | .downstream => true
  | .upstream => false

end Direction

/-- Options shared by one-shot and interactive queries. -/
structure QueryOptions where
  direction : Direction := .both
  depth : Nat := 1
  limit : Nat := 20
  includeInternal : Bool := false

/-- A source location. Lines and columns are both one-based for CLI consumers. -/
structure SourceLocation where
  moduleName : String
  file : Option String
  line : Nat
  column : Nat
  endLine : Nat
  endColumn : Nat
  deriving ToJson

/-- The agent-facing description of a declaration. -/
structure DeclarationView where
  name : String
  signature : String
  source : SourceLocation
  deriving ToJson

/-- A bounded result page together with its size before truncation. -/
structure Page (α : Type) where
  total : Nat
  items : Array α
  deriving ToJson

/-- A dependency edge with one lightweight path witness. -/
structure Relation (α β : Type) where
  distance : Nat
  via : Option β
  declaration : α
  deriving ToJson

abbrev RelationList := Page (Relation DeclarationView String)

/-- Stable JSON payload for a declaration-neighborhood query. -/
structure QueryResult where
  query : String
  target : DeclarationView
  upstream : RelationList
  downstream : RelationList
  deriving ToJson

/-- A domain failure with ranked candidates in the representation needed by the caller. -/
structure QueryError (α : Type) where
  error : String
  candidates : Array α := #[]
  deriving ToJson

abbrev QueryFailure := QueryError DeclarationView

/-- Stable JSON payload for name search. -/
structure SearchResult extends Page DeclarationView where
  query : String
  deriving ToJson

end LeanReach
