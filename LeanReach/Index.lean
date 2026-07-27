import Lean.Meta
import Lean.Util.FoldConsts
import LeanReach.BlackListed

namespace LeanReach

open Lean

/-- Searchable names and cached direct dependency postings in both directions. -/
structure Index where
  private names : Array (Name × String)
  private forward : NameMap NameSet
  private reverse : NameMap NameSet
  deriving Inhabited

private def usedConstants (included : NameHashSet) (name : Name) (info : ConstantInfo) : NameSet :=
  info.getUsedConstantsAsSet.filter fun dependency =>
    dependency != name && included.contains dependency

def Index.build : CoreM Index := do
  let env ← getEnv
  let mut names := #[]
  let mut included : NameHashSet := {}
  for (name, _) in env.constants do
    unless ← isBlackListed name do
      names := names.push (name, name.toString.toLower)
      included := included.insert name
  let mut forward : NameMap NameSet := {}
  let mut reverse : NameMap NameSet := {}
  for (name, info) in env.constants do
    if included.contains name then
      let dependencies := usedConstants included name info
      unless dependencies.isEmpty do
        forward := NameMap.insert forward name dependencies
      for dependency in dependencies do
        reverse := NameMap.insert reverse dependency ((reverse.getD dependency {}).insert name)
  return {
    names := names.qsort fun a b => Name.lt a.1 b.1
    forward
    reverse
  }

private def Index.matchBuckets (index : Index) (query : String) (limit : Nat) :
    Array (Array Name) := Id.run do
  let query := query.toLower
  let suffix := "." ++ query
  let mut buckets : Array (Array Name) := #[#[], #[], #[]]
  for (name, lower) in index.names do
    let score? :=
      if lower == query then some 0
      else if lower.endsWith suffix then some 1
      else if lower.contains query then some 2
      else none
    if let some score := score? then
      if buckets[score]!.size < limit then
        buckets := buckets.modify score (·.push name)
  return buckets

def Index.search (index : Index) (query : String) (limit : Nat := 20) : Array Name :=
  (index.matchBuckets query limit).flatten.take limit

def Index.resolve (index : Index) (query : String) : Except String Name := do
  let exact := query.toName
  if index.names.binSearchContains (exact, "") fun a b => Name.lt a.1 b.1 then return exact
  let candidates := (index.matchBuckets query 10).find? (not ∘ Array.isEmpty) |>.getD #[]
  if candidates.size == 1 then return candidates[0]!
  if candidates.isEmpty then throw s!"no declaration name contains '{query}'"
  throw s!"ambiguous declaration '{query}':\n{String.intercalate "\n" <|
    candidates.toList.map fun name => s!"  {name}"}"

def Index.upstream (index : Index) (name : Name) : NameSet :=
  index.forward.getD name {}

def Index.downstream (index : Index) (name : Name) : NameSet :=
  index.reverse.getD name {}

def Index.declarationCount (index : Index) : Nat :=
  index.names.size

def Index.documentFrequency (index : Index) (name : Name) : Nat :=
  (index.downstream name).size

end LeanReach
