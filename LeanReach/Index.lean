import Lean.Data.Name
import Lean.Data.Trie
import LeanReach.NameSearch
import LeanReach.Rank

namespace LeanReach

open Lean

/-- Searchable names and their defining modules. Array positions are declaration IDs. -/
abbrev CatalogEntry := Name × Name
abbrev Catalog := Array CatalogEntry × Data.Trie (Array UInt32)

structure Relations where
  forward : Array (Array UInt32)
  reverse : Array (Array UInt32)
  upstreamPrior : Array Float
  downstreamPrior : Array Float
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
  private upstreamPrior : Array Float
  private downstreamPrior : Array Float
  deriving Inhabited

abbrev IndexedDeclaration := Name × Name × NameSet

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
    for trigram in NameSearch.trigrams name.toString.toLower do
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
  return {
    entries
    trigrams := trigramIndex
    forward
    reverse
    upstreamPrior := Rank.priors forward reverse true
    downstreamPrior := Rank.priors forward reverse false
  }

def Index.catalog (index : Index) : Catalog :=
  (index.entries, index.trigrams)

def Index.relations (index : Index) : Relations :=
  {
    forward := index.forward
    reverse := index.reverse
    upstreamPrior := index.upstreamPrior
    downstreamPrior := index.downstreamPrior
  }

def Index.ofParts (catalog : Catalog) (relations : Relations) : Index :=
  {
    entries := catalog.1
    trigrams := catalog.2
    forward := relations.forward
    reverse := relations.reverse
    upstreamPrior := relations.upstreamPrior
    downstreamPrior := relations.downstreamPrior
  }

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
    (ids : Array UInt32) (upstream : Bool) (limit : Nat) : Array UInt32 :=
  let (sourceName, sourceModule) := index.entries[source.toNat]!
  let source : LocatedName := { name := sourceName, moduleName := sourceModule }
  Rank.select source ids
    (fun candidate =>
      let (name, moduleName) := index.entries[candidate.toNat]!
      { name, moduleName })
    (fun candidate =>
      if upstream then index.upstreamPrior[candidate.toNat]!
      else index.downstreamPrior[candidate.toNat]!)
    limit

private def Index.relatedIds (index : Index) (source : UInt32)
    (upstream : Bool) (limit : Nat) : Array UInt32 :=
  let ids := if upstream then index.forward[source.toNat]! else index.reverse[source.toNat]!
  index.rankIds source ids upstream limit

private def Index.locatedAt (index : Index) (id : UInt32) : LocatedName :=
  let (name, moduleName) := index.entries[id.toNat]!
  { name, moduleName }

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

def Index.forwardCount (index : Index) (name : Name) : Nat :=
  index.findId? name |>.map (index.forward[·.toNat]!.size) |>.getD 0

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
    for trigram in NameSearch.trigrams query do
      let some ids := index.trigrams.find? trigram | return #[]
      if best.all (ids.size < ·.size) then best := some ids
    return best.getD #[]

private def Index.matches (index : Index) (query : String) (limit : Nat) :
    Array (Array Name) :=
  let query := query.toLower
  NameSearch.buckets query (index.candidates query)
    (fun id => index.entries[id.toNat]?.map (·.1)) id limit

def Index.search (index : Index) (query : String) (limit : Nat := 20) : Array Name :=
  (index.matches query limit).flatten.take limit

def Index.resolve (index : Index) (query : String) : Except String Name := do
  let exact := query.toName
  if index.findId? exact |>.isSome then return exact
  let candidates := (index.matches query 10).find?
    (not ∘ Array.isEmpty) |>.getD #[]
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
