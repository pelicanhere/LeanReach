import Lean.Data.Name
import Lean.Data.Trie
import LeanReach.Search.Pattern
import LeanReach.Search.Rank
import LeanReach.Search.Resolve
import LeanReach.Search.Types

namespace LeanReach

open Lean

/-- Searchable names and their defining modules. Array positions are declaration IDs. -/
abbrev Catalog := Array LocatedName × Data.Trie (Array UInt32)

structure Relations where
  forward : Array (Array UInt32)
  reverse : Array (Array UInt32)
  upstreamPrior : Array Float
  downstreamPrior : Array Float
  deriving Inhabited

abbrev CachedQuery := Neighborhood LocatedName

def cachedQueryLimit := 10

structure Index extends Relations where
  private entries : Array LocatedName
  private trigrams : Data.Trie (Array UInt32)

def Index.build (declarations : Array (Name × Name × NameSet)) : Index := Id.run do
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
  let mut trigramIndex : Data.Trie (Array UInt32) := {}
  for (name, moduleName, _) in declarations do
    let id := entries.size.toUInt32
    entries := entries.push { name, moduleName }
    ids := ids.insert name id
    let mut seen : Std.HashSet String := {}
    for trigram in NameSearch.trigrams (NameSearch.normalizedName name) do
      unless seen.contains trigram do
        seen := seen.insert trigram
        trigramIndex := trigramIndex.upsert trigram fun ids =>
          (ids.getD #[]).push id
  let mut forward := Array.replicate entries.size #[]
  let mut reverse := Array.replicate entries.size #[]
  for ((name, _, used), source) in declarations.zipIdx do
    let source := source.toUInt32
    for dependency in used do
      if dependency != name then
        if let some target := ids.find? dependency then
          forward := forward.modify source.toNat (·.push target)
          reverse := reverse.modify target.toNat (·.push source)
  return {
    entries
    trigrams := trigramIndex
    toRelations := {
      forward
      reverse
      upstreamPrior := Rank.priors forward reverse true
      downstreamPrior := Rank.priors forward reverse false
    }
  }

def Index.catalog (index : Index) : Catalog :=
  (index.entries, index.trigrams)

def Index.ofParts (catalog : Catalog) (relations : Relations) : Index :=
  {
    entries := catalog.1
    trigrams := catalog.2
    toRelations := relations
  }

private def Index.findId? (index : Index) (name : Name) : Option UInt32 := Id.run do
  let mut lo := 0
  let mut hi := index.entries.size
  while lo < hi do
    let mid := (lo + hi) / 2
    let candidate := index.entries[mid]!.name
    if candidate == name then return some mid.toUInt32
    if Name.lt candidate name then lo := mid + 1 else hi := mid
  return none

def Index.size (index : Index) : Nat :=
  index.entries.size

private def Index.rankIds (index : Index) (source : UInt32)
    (ids : Array UInt32) (upstream : Bool) (limit : Nat) : Array UInt32 :=
  let source := index.entries[source.toNat]!
  Rank.select source ids
    (fun candidate => index.entries[candidate.toNat]!)
    (fun candidate =>
      if upstream then index.upstreamPrior[candidate.toNat]!
      else index.downstreamPrior[candidate.toNat]!)
    limit

private def Index.relatedIds (index : Index) (source : UInt32)
    (upstream : Bool) (limit : Nat) : Array UInt32 :=
  let ids := if upstream then index.forward[source.toNat]! else index.reverse[source.toNat]!
  index.rankIds source ids upstream limit

private def Index.locatedAt (index : Index) (id : UInt32) : LocatedName :=
  index.entries[id.toNat]!

def Index.located? (index : Index) (name : Name) : Option LocatedName :=
  index.findId? name |>.map index.locatedAt

def Index.relationCounts (index : Index) (name : Name) : Nat × Nat :=
  match index.findId? name with
  | some id => (index.reverse[id.toNat]!.size, index.forward[id.toNat]!.size)
  | none => (0, 0)

def Index.cachedQueryAt! (index : Index) (id : Nat) : CachedQuery :=
  let id := id.toUInt32
  {
    target := index.locatedAt id
    upstream := (index.relatedIds id true cachedQueryLimit).map index.locatedAt
    downstream := (index.relatedIds id false cachedQueryLimit).map index.locatedAt
  }

private def Index.resolveMatches (index : Index) (query : String) (limit : Nat) :
    Array (Array LocatedName) :=
  let query := query.toLower
  let find size candidateAt :=
    NameResolve.buckets query size candidateAt
      (fun id => index.entries[id.toNat]?) (·.name) limit
  if query.length < 3 then
    find index.entries.size (fun id => id.toUInt32)
  else
    let gram? := NameSearch.rarestTrigram? (NameSearch.trigrams query)
      (index.trigrams.find? · |>.map (·.size))
    let candidates := gram?.bind index.trigrams.find? |>.getD #[]
    find candidates.size (fun id => candidates[id]!)

def Index.searchAll (index : Index) (pattern : SearchPattern)
    (limit : Nat := 20) : Array Name :=
  pattern.collect index.entries.size (fun id => id.toUInt32)
    (fun id => index.entries[id.toNat]?) (·.name) limit |>.map (·.name)

def Index.search (index : Index) (pattern : SearchPattern)
    (limit : Nat := 20) : Array Name :=
  match pattern.candidatePlan with
  | .all => index.searchAll pattern limit
  | .empty => #[]
  | plan@(.postings _) =>
    match plan.select (index.trigrams.find? · |>.map (·.size)) with
    | .empty => #[]
    | .postings alternatives =>
      let ids := alternatives.foldl (init := #[]) fun ids grams =>
        let candidates := grams[0]? >>= index.trigrams.find? |>.getD #[]
        SearchPattern.unionIds ids candidates
      pattern.collect ids.size (fun id => ids[id]!)
        (fun id => index.entries[id.toNat]?) (·.name) limit |>.map (·.name)
    | .all => index.searchAll pattern limit

def Index.resolve (index : Index) (query : String) : Except String Name := do
  let exact := query.toName
  if index.findId? exact |>.isSome then return exact
  let candidates := NameResolve.bestBucket (index.resolveMatches query 10)
  if candidates.size == 1 then return candidates[0]!.name
  if candidates.isEmpty then throw <| NameResolve.noMatchMessage query
  throw <| NameResolve.ambiguityMessage query candidates

private def Index.related (index : Index) (name : Name) (upstream : Bool)
    (limit : Nat) : Array Name :=
  match index.findId? name with
  | some id =>
    (index.relatedIds id upstream limit).map fun id => index.entries[id.toNat]!.name
  | none => #[]

def Index.upstream (index : Index) (name : Name) (limit : Nat) : Array Name :=
  index.related name true limit

def Index.downstream (index : Index) (name : Name) (limit : Nat) : Array Name :=
  index.related name false limit

def Index.moduleOf? (index : Index) (name : Name) : Option Name :=
  index.findId? name |>.map fun id => index.entries[id.toNat]!.moduleName

def Index.modules (index : Index) : Array Name := Id.run do
  let mut seen : NameHashSet := {}
  let mut modules := #[]
  for entry in index.entries do
    unless seen.contains entry.moduleName do
      seen := seen.insert entry.moduleName
      modules := modules.push entry.moduleName
  return modules

def Index.declarationsByModule (index : Index) : NameMap (Array Name) :=
  index.entries.foldl (init := {}) fun modules entry =>
    modules.alter entry.moduleName fun names => some ((names.getD #[]).push entry.name)

end LeanReach
