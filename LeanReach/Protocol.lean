import Lean.Data.Json

namespace LeanReach

open Lean

/-- Which side of a declaration's dependency neighborhood to inspect. -/
inductive Direction where
  | both
  | upstream
  | downstream
  deriving Repr, BEq

namespace Direction

def includesUpstream : Direction → Bool
  | .both | .upstream => true
  | .downstream => false

def includesDownstream : Direction → Bool
  | .both | .downstream => true
  | .upstream => false

end Direction

/-- Which Lean artifact defines dependency edges. -/
inductive DependencyMode where
  | source
  | kernel
  deriving Repr, BEq

namespace DependencyMode

def label : DependencyMode → String
  | .source => "source"
  | .kernel => "kernel"

end DependencyMode

/-- Options shared by one-shot and interactive queries. -/
structure QueryOptions where
  mode : DependencyMode := .source
  direction : Direction := .both
  depth : Nat := 1
  limit : Nat := 20
  includeInternal : Bool := false
  deriving Repr

/-- A source location. Lines and columns are both one-based for CLI consumers. -/
structure SourceLocation where
  moduleName : Option String
  file : Option String
  line : Option Nat
  column : Option Nat
  endLine : Option Nat
  endColumn : Option Nat
  deriving Repr, ToJson

/-- The agent-facing description of a declaration. -/
structure DeclarationView where
  name : String
  kind : String
  source : SourceLocation
  deriving Repr, ToJson

/-- A bounded result page together with its size before truncation. -/
structure Page (α : Type) where
  total : Nat
  items : Array α
  deriving Repr, ToJson

/-- A dependency edge with one lightweight path witness. -/
structure Relation (α β : Type) where
  distance : Nat
  via : Option β
  declaration : α
  deriving Repr, ToJson

abbrev RelationView := Relation DeclarationView String
abbrev RelationList := Page RelationView

/-- Stable JSON payload for a declaration-neighborhood query. -/
structure QueryResult where
  schemaVersion : Nat := 1
  query : String
  mode : String
  target : DeclarationView
  upstream : RelationList
  downstream : RelationList
  deriving Repr, ToJson

/-- A domain failure with ranked candidates in the representation needed by the caller. -/
structure QueryError (α : Type) where
  schemaVersion : Nat := 1
  error : String
  candidates : Array α := #[]
  deriving Repr, ToJson

abbrev QueryFailure := QueryError DeclarationView

/-- Stable JSON payload for name search. -/
structure SearchResult extends Page DeclarationView where
  schemaVersion : Nat := 1
  query : String
  deriving Repr, ToJson

end LeanReach
