import Lean.Data.Name
import Lean.Data.Trie

namespace LeanReach

open Lean

/-- Searchable names and cached direct dependency postings in both directions. -/
abbrev CatalogEntry := Name × String × Name × UInt32
abbrev Catalog := Array CatalogEntry × Data.Trie (Array UInt32)
abbrev Relations := Array (Array UInt32) × Array (Array UInt32)

structure Index where
  private entries : Array CatalogEntry
  private trigrams : Data.Trie (Array UInt32)
  private forward : Array (Array UInt32)
  private reverse : Array (Array UInt32)
  deriving Inhabited

abbrev IndexedDeclaration := Name × Name × NameSet

private def stringTrigrams (value : String) : Array String := Id.run do
  let mut result := #[]
  let length := value.length
  for offset in [0:length] do
    if length < offset + 3 then break
    result := result.push ((value.drop offset).take 3).copy
  return result

private def commonPrefixLength : List Name → List Name → Nat
  | a :: as, b :: bs => if a == b then commonPrefixLength as bs + 1 else 0
  | _, _ => 0

private def locality (entries : Array CatalogEntry) (source candidate : UInt32) : Nat :=
  let (sourceName, _, sourceModule, _) := entries[source.toNat]!
  let (candidateName, _, candidateModule, _) := entries[candidate.toNat]!
  (if sourceModule == candidateModule then 64 else 0) +
    16 * commonPrefixLength sourceName.components candidateName.components +
    4 * commonPrefixLength sourceModule.components candidateModule.components

def Index.build (declarations : Array IndexedDeclaration) : Index := Id.run do
  let declarations := declarations.qsort fun a b => Name.lt a.1 b.1
  let mut entries := #[]
  let mut ids : NameMap UInt32 := {}
  for (name, moduleName, _) in declarations do
    let id := entries.size.toUInt32
    entries := entries.push (name, name.toString.toLower, moduleName, id)
    ids := ids.insert name id
  let mut trigramIndex : Data.Trie (Array UInt32) := {}
  for (_, lower, _, id) in entries do
    let mut seen : Std.HashSet String := {}
    for trigram in stringTrigrams lower do
      unless seen.contains trigram do
        seen := seen.insert trigram
        trigramIndex := trigramIndex.upsert trigram fun ids => (ids.getD #[]).push id
  let mut forward := Array.replicate entries.size #[]
  let mut reverse := Array.replicate entries.size #[]
  for (name, _, used) in declarations do
    let some source := ids.find? name | continue
    for dependency in used do
      if dependency != name then
        if let some target := ids.find? dependency then
          forward := forward.modify source.toNat (·.push target)
          reverse := reverse.modify target.toNat (·.push source)
  return { entries, trigrams := trigramIndex, forward, reverse }

def Index.catalog (index : Index) : Catalog :=
  (index.entries, index.trigrams)

def Index.relations (index : Index) : Relations :=
  (index.forward, index.reverse)

def Index.ofParts (catalog : Catalog) (relations : Relations) : Index :=
  { entries := catalog.1, trigrams := catalog.2, forward := relations.1, reverse := relations.2 }

private def Index.findEntry? (index : Index) (name : Name) : Option CatalogEntry :=
  index.entries.binSearch (name, "", .anonymous, 0) fun a b => Name.lt a.1 b.1

private def Index.namesAt (index : Index) (ids : Array UInt32) : Array Name :=
  ids.map fun id => index.entries[id.toNat]!.1

private def Index.rankIds (index : Index) (source : UInt32)
    (ids : Array UInt32) (upstream : Bool) : Array UInt32 :=
  (ids.map fun id => (locality index.entries source id, index.reverse[id.toNat]!.size, id))
    |>.qsort (fun (scoreA, frequencyA, a) (scoreB, frequencyB, b) =>
      if scoreA != scoreB then scoreA > scoreB
      else if frequencyA != frequencyB then
        if upstream then frequencyA < frequencyB else frequencyA > frequencyB
      else Name.lt index.entries[a.toNat]!.1 index.entries[b.toNat]!.1)
    |>.map (·.2.2)

private def Index.candidates (index : Index) (query : String) : Array UInt32 :=
  if query.length < 3 then
    index.entries.map fun (_, _, _, id) => id
  else Id.run do
    let mut best : Option (Array UInt32) := none
    for trigram in stringTrigrams query do
      let some ids := index.trigrams.find? trigram | return #[]
      if best.all (ids.size < ·.size) then best := some ids
    return best.getD #[]

private def Index.matchBuckets (index : Index) (query : String) (limit : Nat) :
    Array (Array Name) := Id.run do
  let query := query.toLower
  let suffix := "." ++ query
  let mut buckets : Array (Array Name) := #[#[], #[], #[]]
  for id in index.candidates query do
    let (name, lower, _, _) := index.entries[id.toNat]!
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

def Index.rankedUpstream (index : Index) (name : Name) : Array Name :=
  match index.findEntry? name with
  | some (_, _, _, id) => index.namesAt (index.rankIds id index.forward[id.toNat]! true)
  | none => #[]

def Index.rankedDownstream (index : Index) (name : Name) : Array Name :=
  match index.findEntry? name with
  | some (_, _, _, id) => index.namesAt (index.rankIds id index.reverse[id.toNat]! false)
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

def Index.namesInModules (index : Index) (modules : Array Name) : Array Name :=
  let wanted := modules.foldl (init := ({} : NameHashSet)) (·.insert ·)
  index.entries.filterMap fun (name, _, moduleName, _) =>
    if wanted.contains moduleName then some name else none

def Index.declarationCount (index : Index) : Nat :=
  index.entries.size

def Index.documentFrequency (index : Index) (name : Name) : Nat :=
  match index.findEntry? name with
  | some (_, _, _, id) => index.reverse[id.toNat]!.size
  | none => 0

end LeanReach
