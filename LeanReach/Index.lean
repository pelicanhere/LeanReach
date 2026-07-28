import Lean.Data.Name
import Lean.Data.Trie
import Batteries.Data.BinaryHeap.Basic

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

private def lastComponent : Name → String
  | .str _ value => value
  | .num _ value => toString value
  | .anonymous => ""

private def nameAffinity (source : String) (sourceParts : List String)
    (candidate : Name) : Float :=
  let candidate := lastComponent candidate
  let exact := if source == candidate then 3.5 else 0.0
  if sourceParts.isEmpty then exact
  else
    let candidateParts := candidate.toLower.splitOn "_"
    let shared := sourceParts.countP candidateParts.contains
    exact + 1.5 * shared.toFloat

private def locality (entries : Array CatalogEntry) (sourceModule : Name)
    (sourceNameParts sourceModuleParts : List Name) (sourceLeaf : String)
    (sourceParts : List String) (candidate : UInt32) : Float :=
  let (candidateName, _, candidateModule, _) := entries[candidate.toNat]!
  (if sourceModule == candidateModule then 8.0 else 0.0) +
    4.0 * (commonPrefixLength sourceNameParts candidateName.components).toFloat +
    (commonPrefixLength sourceModuleParts candidateModule.components).toFloat +
    nameAffinity sourceLeaf sourceParts candidateName

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

def Index.size (index : Index) : Nat :=
  index.entries.size

def Index.idOf? (index : Index) (name : Name) : Option UInt32 :=
  index.findEntry? name |>.map fun (_, _, _, id) => id

private def Index.namesAt (index : Index) (ids : Array UInt32) : Array Name :=
  ids.map fun id => index.entries[id.toNat]!.1

private def Index.rankIds (index : Index) (source : UInt32)
    (ids : Array UInt32) (upstream : Bool) (limit : Nat) : Array UInt32 := Id.run do
  if limit == 0 then return #[]
  let (sourceName, _, sourceModule, _) := index.entries[source.toNat]!
  let sourceNameParts := sourceName.components
  let sourceModuleParts := sourceModule.components
  let sourceLeaf := lastComponent sourceName
  let sourceParts :=
    if sourceLeaf.contains '_' then
      (sourceLeaf.toLower.splitOn "_").filter (·.length ≥ 3)
    else []
  let score (candidate : UInt32) :=
    let df := index.reverse[candidate.toNat]!.size.toFloat
    let frequency :=
      if upstream then
        let n := index.entries.size.toFloat
        Float.log (1.0 + (n - df + 0.5) / (df + 0.5))
      else
        Float.log (1.0 + df)
    locality index.entries sourceModule sourceNameParts sourceModuleParts
      sourceLeaf sourceParts candidate + frequency
  let better := fun (scoreA, a) (scoreB, b) =>
      if scoreA != scoreB then scoreA > scoreB
      else Name.lt index.entries[a.toNat]!.1 index.entries[b.toNat]!.1
  let best :=
    if ids.size ≤ limit then ids.map fun id => (score id, id)
    else
      Id.run do
        let mut heap := Batteries.BinaryHeap.empty better
        for id in ids do
          let item := (score id, id)
          heap :=
            if heap.size < limit then heap.insert item
            else (heap.insertExtractMax item).2
        return heap.arr
  return (best.qsort better).map (·.2)

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

private def Index.related (index : Index) (name : Name) (upstream : Bool)
    (limit : Nat) : Array Name :=
  match index.findEntry? name with
  | some (_, _, _, id) =>
    let ids := if upstream then index.forward[id.toNat]! else index.reverse[id.toNat]!
    index.namesAt (index.rankIds id ids upstream limit)
  | none => #[]

def Index.upstream (index : Index) (name : Name) (limit : Nat) : Array Name :=
  index.related name true limit

def Index.downstream (index : Index) (name : Name) (limit : Nat) : Array Name :=
  index.related name false limit

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

def Index.declarationsByModule (index : Index) : NameMap (Array Name) :=
  index.entries.foldl (init := {}) fun modules (name, _, moduleName, _) =>
    modules.insert moduleName ((modules.find? moduleName).getD #[] |>.push name)

end LeanReach
