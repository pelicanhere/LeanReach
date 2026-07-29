import Lean.Data.Name
import Lean.Data.Trie

namespace LeanReach

open Lean

universe u

/-- Searchable names and their defining modules. Array positions are declaration IDs. -/
abbrev CatalogEntry := Name × Name
abbrev Catalog := Array CatalogEntry × Data.Trie (Array UInt32)
abbrev Relations := Array (Array UInt32) × Array (Array UInt32)

structure LocatedName where
  name : Name
  moduleName : Name
  deriving Inhabited

structure CachedQuery where
  target : LocatedName
  upstream : Array LocatedName
  downstream : Array LocatedName

def cachedQueryLimit := 10

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

private def significantParts (name : Name) : List String :=
  let leaf := (lastComponent name).toLower
  if leaf.contains '_' then (leaf.splitOn "_").filter (·.length ≥ 3) else []

private def nameAffinity (source : String) (sourceParts : List String)
    (candidate : Name) : Float :=
  let candidate := lastComponent candidate
  let exact := if source == candidate then 3.5 else 0.0
  if sourceParts.isEmpty then exact
  else
    let candidateParts := candidate.toLower.splitOn "_"
    let shared := sourceParts.countP candidateParts.contains
    exact + 1.5 * shared.toFloat

private def locality (sourceModule : Name)
    (sourceNameParts sourceModuleParts : List Name) (sourceLeaf : String)
    (sourceParts : List String) (candidate : LocatedName) : Float :=
  let { name := candidateName, moduleName := candidateModule } := candidate
  (if sourceModule == candidateModule then 8.0 else 0.0) +
    4.0 * (commonPrefixLength sourceNameParts candidateName.components).toFloat +
    (commonPrefixLength sourceModuleParts candidateModule.components).toFloat +
    nameAffinity sourceLeaf sourceParts candidateName

private def heapifyDown {α : Type u} [Inhabited α] (lt : α → α → Bool)
    (items : Array α) : Array α := Id.run do
  let mut items := items
  let mut parent : Nat := 0
  while 2 * parent + 1 < items.size do
    let left := 2 * parent + 1
    let right := left + 1
    let child : Nat :=
      if right < items.size && lt items[left]! items[right]! then right else left
    if lt items[parent]! items[child]! then
      items := items.swapIfInBounds parent child
      parent := child
    else break
  return items

private def heapInsert {α : Type u} [Inhabited α] (lt : α → α → Bool)
    (items : Array α) (item : α) : Array α := Id.run do
  let mut items := items.push item
  let mut child : Nat := items.size - 1
  while child > 0 do
    let parent := (child - 1) / 2
    if lt items[parent]! items[child]! then
      items := items.swapIfInBounds parent child
      child := parent
    else break
  return items

private def heapKeepBest {α : Type u} [Inhabited α] (lt : α → α → Bool)
    (items : Array α) (item : α) : Array α :=
  match items[0]? with
  | some worst => if lt item worst then heapifyDown lt (items.set! 0 item) else items
  | none => items

private def rankPositions (size limit : Nat) (score : Nat → Float)
    (name : Nat → Name) : Array Nat := Id.run do
  if limit == 0 || size == 0 then return #[]
  if size == 1 then return #[0]
  let better := fun (scoreA, a) (scoreB, b) =>
    if scoreA != scoreB then scoreA > scoreB else Name.lt (name a) (name b)
  let best :=
    if size ≤ limit then
      (Array.range size).map fun id => (score id, id)
    else
      Id.run do
        let mut heap := #[]
        for id in [0:size] do
          let item := (score id, id)
          heap :=
            if heap.size < limit then heapInsert better heap item
            else heapKeepBest better heap item
        return heap
  return (best.qsort better).map (·.2)

private def relationScore (total reverseCount : Nat) (source : LocatedName)
    (sourceNameParts sourceModuleParts : List Name) (sourceLeaf : String)
    (sourceParts : List String) (upstream : Bool) (candidate : LocatedName) : Float :=
  let df := reverseCount.toFloat
  let frequency :=
    if upstream then
      let n := total.toFloat
      Float.log (1.0 + (n - df + 0.5) / (df + 0.5))
    else
      Float.log (1.0 + df)
  locality source.moduleName sourceNameParts sourceModuleParts sourceLeaf sourceParts candidate +
    frequency

def Index.build (declarations : Array IndexedDeclaration) : Index := Id.run do
  let mut byName : NameMap (Name × NameSet) := {}
  for (name, moduleName, used) in declarations do
    let (owner, previous) := (byName.find? name).getD (moduleName, {})
    byName := byName.insert name (owner, previous ++ used)
  let mut declarations := #[]
  for (name, moduleName, used) in byName do
    declarations := declarations.push (name, moduleName, used)
  declarations := declarations.qsort fun a b => Name.lt a.1 b.1
  let mut entries := #[]
  let mut ids : NameMap UInt32 := {}
  for (name, moduleName, _) in declarations do
    let id := entries.size.toUInt32
    entries := entries.push (name, moduleName)
    ids := ids.insert name id
  let mut trigramIndex : Data.Trie (Array UInt32) := {}
  for ((name, _), id) in entries.zipIdx do
    let mut seen : Std.HashSet String := {}
    for trigram in stringTrigrams name.toString.toLower do
      unless seen.contains trigram do
        seen := seen.insert trigram
        trigramIndex := trigramIndex.upsert trigram fun ids =>
          (ids.getD #[]).push id.toUInt32
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

private def Index.findId? (index : Index) (name : Name) : Option UInt32 := Id.run do
  let mut lo := 0
  let mut hi := index.entries.size
  while lo < hi do
    let mid := (lo + hi) / 2
    let candidate := index.entries[mid]!.1
    if candidate == name then return some mid.toUInt32
    if Name.lt candidate name then lo := mid + 1 else hi := mid
  return none

def Index.size (index : Index) : Nat :=
  index.entries.size

private def Index.namesAt (index : Index) (ids : Array UInt32) : Array Name :=
  ids.map fun id => index.entries[id.toNat]!.1

private def Index.rankIds (index : Index) (source : UInt32)
    (ids : Array UInt32) (upstream : Bool) (limit : Nat) : Array UInt32 := Id.run do
  let (sourceName, sourceModule) := index.entries[source.toNat]!
  let source : LocatedName := { name := sourceName, moduleName := sourceModule }
  let sourceNameParts := sourceName.components
  let sourceModuleParts := sourceModule.components
  let sourceLeaf := lastComponent sourceName
  let sourceParts := significantParts sourceName
  let positions := rankPositions ids.size limit
    (fun position =>
      let candidate := ids[position]!
      let (name, moduleName) := index.entries[candidate.toNat]!
      relationScore index.size index.reverse[candidate.toNat]!.size source
        sourceNameParts sourceModuleParts sourceLeaf sourceParts upstream { name, moduleName })
    (fun position => index.entries[ids[position]!.toNat]!.1)
  return positions.map fun position => ids[position]!

private def Index.relatedIds (index : Index) (source : UInt32)
    (upstream : Bool) (limit : Nat) : Array UInt32 :=
  let ids := if upstream then index.forward[source.toNat]! else index.reverse[source.toNat]!
  index.rankIds source ids upstream limit

private def Index.locatedAt (index : Index) (id : UInt32) : LocatedName :=
  let (name, moduleName) := index.entries[id.toNat]!
  { name, moduleName }

def rankLocated (source : LocatedName) (candidates : Array LocatedName)
    (total : Nat) (reverseCount : Name → Nat) (upstream : Bool)
    (limit : Nat) : Array LocatedName := Id.run do
  let sourceNameParts := source.name.components
  let sourceModuleParts := source.moduleName.components
  let sourceLeaf := lastComponent source.name
  let sourceParts := significantParts source.name
  let positions := rankPositions candidates.size limit
    (fun position =>
      let candidate := candidates[position]!
      relationScore total (reverseCount candidate.name) source sourceNameParts
        sourceModuleParts sourceLeaf sourceParts upstream candidate)
    (fun position => candidates[position]!.name)
  return positions.map fun position => candidates[position]!

def Index.located? (index : Index) (name : Name) : Option LocatedName :=
  index.findId? name |>.map index.locatedAt

def Index.relatedLocated (index : Index) (name : Name)
    (upstream : Bool) : Array LocatedName :=
  match index.findId? name with
  | some id =>
    (if upstream then index.forward[id.toNat]! else index.reverse[id.toNat]!).map index.locatedAt
  | none => #[]

def Index.reverseCount (index : Index) (name : Name) : Nat :=
  index.findId? name |>.map (index.reverse[·.toNat]!.size) |>.getD 0

private def Index.cachedAt (index : Index) (id : UInt32) : CachedQuery :=
  {
    target := index.locatedAt id
    upstream := (index.relatedIds id true cachedQueryLimit).map index.locatedAt
    downstream := (index.relatedIds id false cachedQueryLimit).map index.locatedAt
  }

def Index.cachedQueryAt! (index : Index) (id : Nat) : CachedQuery :=
  index.cachedAt id.toUInt32

private def Index.candidates (index : Index) (query : String) : Array UInt32 :=
  if query.length < 3 then
    index.entries.mapIdx fun id _ => id.toUInt32
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
    let name := index.entries[id.toNat]!.1
    let lower := name.toString.toLower
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
  if index.findId? exact |>.isSome then return exact
  let candidates := (index.matchBuckets query 10).find? (not ∘ Array.isEmpty) |>.getD #[]
  if candidates.size == 1 then return candidates[0]!
  if candidates.isEmpty then throw s!"no declaration name contains '{query}'"
  throw s!"ambiguous declaration '{query}':\n{String.intercalate "\n" <|
    candidates.toList.map fun name => s!"  {name}"}"

private def Index.related (index : Index) (name : Name) (upstream : Bool)
    (limit : Nat) : Array Name :=
  match index.findId? name with
  | some id =>
    index.namesAt (index.relatedIds id upstream limit)
  | none => #[]

def Index.upstream (index : Index) (name : Name) (limit : Nat) : Array Name :=
  index.related name true limit

def Index.downstream (index : Index) (name : Name) (limit : Nat) : Array Name :=
  index.related name false limit

def Index.moduleOf? (index : Index) (name : Name) : Option Name :=
  index.findId? name |>.map fun id => index.entries[id.toNat]!.2

def Index.modules (index : Index) : Array Name := Id.run do
  let mut seen : NameHashSet := {}
  let mut modules := #[]
  for (_, moduleName) in index.entries do
    unless seen.contains moduleName do
      seen := seen.insert moduleName
      modules := modules.push moduleName
  return modules

def Index.declarationsByModule (index : Index) : NameMap (Array Name) :=
  index.entries.foldl (init := {}) fun modules (name, moduleName) =>
    modules.insert moduleName ((modules.find? moduleName).getD #[] |>.push name)

end LeanReach
