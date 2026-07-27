import Lean.CompactedRegion
import Lean.Data.NameMap
import Lean.Server.References

namespace LeanReach.SourceIndex

open Lean

/-- Source-visible declaration metadata recovered from `.ilean`. -/
structure Declaration where
  module : Name
  range : Lsp.DeclInfo

/--
A compact source index: declaration locations plus a direct-reference posting table. It stores no
transitive closure, declaration type, value, or imported `Environment`.
-/
structure Index where
  declarations : NameMap Declaration := {}
  downstream : NameMap NameSet := {}

/-- An index together with the compacted region that owns it, when restored from disk. -/
structure Loaded where
  index : Index
  region? : Option CompactedRegion := none

def Index.declarationCount (index : Index) : Nat := Id.run do
  let mut count := 0
  for _ in index.declarations do
    count := count + 1
  return count

def Index.relationCount (index : Index) : Nat := Id.run do
  let mut count := 0
  for (_, parents) in index.downstream do
    for _ in parents do
      count := count + 1
  return count

end LeanReach.SourceIndex
