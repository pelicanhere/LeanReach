import Lean.Data.NameMap
import Lean.Server.References

namespace LeanReach.SourceIndex

open Lean

/-- Source-visible declaration metadata recovered from `.ilean`. -/
structure Declaration where
  module : Name
  range : Lsp.Range

/--
A compact source index: declaration locations plus a direct-reference posting table. It stores no
transitive closure, declaration type, value, or imported `Environment`.
-/
structure Index where
  declarations : NameMap Declaration := {}
  downstream : NameMap NameSet := {}

def Index.declarationCount (index : Index) : Nat :=
  index.declarations.size

def Index.relationCount (index : Index) : Nat :=
  index.downstream.foldl (init := 0) fun count _ parents => count + parents.size

end LeanReach.SourceIndex
