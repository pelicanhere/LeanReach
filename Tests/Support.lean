import LeanReach

namespace LeanReach.Tests

open Lean

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def expectSome {α : Type} (value : Option α) (message : String) : IO α :=
  match value with
  | some value => pure value
  | none => throw <| IO.userError message

def regex (source : String) : IO SearchPattern :=
  IO.ofExcept <| SearchPattern.compileRegex source |>.mapError IO.userError

unsafe def cachedQuery (roots : Array Name) (name : Name)
    (limits : Limits := {}) : IO CachedQuery := do
  let results ← QueryCache.exactQueries roots name.toString
    { limits with search := 2 }
  let results ← expectSome results s!"query cache is unavailable for '{name}'"
  expectSome (results.find? (·.target.name == name))
    s!"query cache is missing '{name}'"

def checkTable (index : Index) (table : SearchCache.Table) : IO Unit := do
  let entries := index.catalog.1
  let (reverseCounts, forwardCounts) := index.relationCountsById
  check (table.isValid && table.names == entries.map (·.name) &&
      table.reverseCounts == reverseCounts &&
      table.forwardCounts == forwardCounts)
    "declaration table changed index dimensions"
  for (expected, id) in entries.zipIdx do
    let actual := table.locatedAt! id.toUInt32
    check (actual.name == expected.name && actual.moduleName == expected.moduleName)
      s!"declaration table changed '{expected.name}'"

end LeanReach.Tests
