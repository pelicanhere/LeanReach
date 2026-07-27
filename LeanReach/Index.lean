import Lean

namespace LeanReach

open Lean

/-- Searchable names and cached direct dependency postings in both directions. -/
private abbrev Entry := Name × String × Name × UInt32

structure Index where
  private entries : Array Entry
  private forward : Array (Array UInt32)
  private reverse : Array (Array UInt32)
  deriving Inhabited

abbrev IndexedDeclaration := Name × Name × NameSet

def Index.build (declarations : Array IndexedDeclaration) : Index := Id.run do
  let declarations := declarations.qsort fun a b => Name.lt a.1 b.1
  let mut entries := #[]
  let mut ids : NameMap UInt32 := {}
  for (name, moduleName, _) in declarations do
    let id := entries.size.toUInt32
    entries := entries.push (name, name.toString.toLower, moduleName, id)
    ids := ids.insert name id
  let mut forward := Array.replicate entries.size #[]
  let mut reverse := Array.replicate entries.size #[]
  for (name, _, used) in declarations do
    let some source := ids.find? name | continue
    for dependency in used do
      if dependency != name then
        if let some target := ids.find? dependency then
          forward := forward.modify source.toNat (·.push target)
          reverse := reverse.modify target.toNat (·.push source)
  return { entries, forward, reverse }

private def Index.findEntry? (index : Index) (name : Name) : Option Entry :=
  index.entries.binSearch (name, "", .anonymous, 0) fun a b => Name.lt a.1 b.1

private def Index.namesAt (index : Index) (ids : Array UInt32) : Array Name :=
  ids.map fun id => index.entries[id.toNat]!.1

private def Index.matchBuckets (index : Index) (query : String) (limit : Nat) :
    Array (Array Name) := Id.run do
  let query := query.toLower
  let suffix := "." ++ query
  let mut buckets : Array (Array Name) := #[#[], #[], #[]]
  for (name, lower, _, _) in index.entries do
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
  if index.findEntry? exact |>.isSome then return exact
  let candidates := (index.matchBuckets query 10).find? (not ∘ Array.isEmpty) |>.getD #[]
  if candidates.size == 1 then return candidates[0]!
  if candidates.isEmpty then throw s!"no declaration name contains '{query}'"
  throw s!"ambiguous declaration '{query}':\n{String.intercalate "\n" <|
    candidates.toList.map fun name => s!"  {name}"}"

def Index.upstream (index : Index) (name : Name) : Array Name :=
  match index.findEntry? name with
  | some (_, _, _, id) => index.namesAt index.forward[id.toNat]!
  | none => #[]

def Index.downstream (index : Index) (name : Name) : Array Name :=
  match index.findEntry? name with
  | some (_, _, _, id) => index.namesAt index.reverse[id.toNat]!
  | none => #[]

def Index.moduleOf? (index : Index) (name : Name) : Option Name :=
  index.findEntry? name |>.map fun (_, _, moduleName, _) => moduleName

def Index.modulesFor (index : Index) (names : Array Name) : Array Name := Id.run do
  let mut seen : NameHashSet := {}
  let mut modules := #[]
  for name in names do
    if let some moduleName := index.moduleOf? name then
      unless seen.contains moduleName do
        seen := seen.insert moduleName
        modules := modules.push moduleName
  return modules

def Index.declarationCount (index : Index) : Nat :=
  index.entries.size

def Index.documentFrequency (index : Index) (name : Name) : Nat :=
  match index.findEntry? name with
  | some (_, _, _, id) => index.reverse[id.toNat]!.size
  | none => 0

end LeanReach
