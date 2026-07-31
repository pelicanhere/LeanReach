import Lean.Data.Name
import Lean.Data.Trie
import LeanReach.Search.Pattern
import LeanReach.Search.Rank
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

structure Index extends Relations where
  private entries : Array LocatedName
  private trigrams : Data.Trie (Array UInt32)
  private rankFeatures : Array Rank.Features

namespace Index

abbrev Declarations := NameMap (Name × Array Name)

def Declarations.add (declarations : Declarations) (name moduleName : Name)
    (used : Array Name) : Declarations :=
  match declarations.find? name with
  | none => declarations.insert name (moduleName, used)
  | some (owner, previous) =>
    declarations.insert name
      (owner, (NameSet.ofArray previous ++ NameSet.ofArray used).toArray)

def buildFrom (byName : Declarations) : Index := Id.run do
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
    for trigram in NameSearch.trigrams
        ((privateToUserName name).toString.toLower) do
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
    rankFeatures := entries.map Rank.features
    toRelations := {
      forward
      reverse
      upstreamPrior := Rank.priors forward reverse true
      downstreamPrior := Rank.priors forward reverse false
    }
  }

def build (declarations : Array (Name × Name × NameSet)) : Index :=
  buildFrom <| declarations.foldl (init := {}) fun result declaration =>
    result.add declaration.1 declaration.2.1 declaration.2.2.toArray

def catalog (index : Index) : Catalog :=
  (index.entries, index.trigrams)

private def findId? (index : Index) (name : Name) : Option UInt32 :=
  NameSearch.findSorted? index.entries.size (index.entries[·]!.name) name
    |>.map (·.toUInt32)

def size (index : Index) : Nat :=
  index.entries.size

private def rankIds (index : Index) (source : UInt32)
    (ids : Array UInt32) (upstream : Bool) (limit : Nat) : Array UInt32 :=
  let sourceId := source.toNat
  let source := index.entries[sourceId]!
  Rank.selectWith source index.rankFeatures[sourceId]! ids
    (fun candidate => index.entries[candidate.toNat]!)
    (fun candidate => index.rankFeatures[candidate.toNat]!)
    (fun candidate =>
      if upstream then index.upstreamPrior[candidate.toNat]!
      else index.downstreamPrior[candidate.toNat]!)
    limit

def relatedIds (index : Index) (source : UInt32)
    (upstream : Bool) (limit : Nat) : Array UInt32 :=
  let ids := if upstream then index.forward[source.toNat]! else index.reverse[source.toNat]!
  index.rankIds source ids upstream limit

def relationCountsById (index : Index) : Array UInt32 × Array UInt32 :=
  (index.reverse.map (·.size.toUInt32), index.forward.map (·.size.toUInt32))

def exactMatches (index : Index) (query : String)
    (limit : Nat) : Array LocatedName :=
  let normalized := query.toLower
  let candidates :=
    if normalized.length < 3 then
      Array.range index.entries.size |>.map (·.toUInt32)
    else
      NameSearch.rarestTrigram? (NameSearch.trigrams normalized)
        (index.trigrams.find? · |>.map (·.size))
        |>.bind index.trigrams.find?
        |>.getD #[]
  let name := query.toName
  candidates.filterMap (fun id => index.entries[id.toNat]?)
    |>.filter (NameSearch.exactMatch name ·.name)
    |>.take limit

def searchAll (index : Index) (pattern : SearchPattern)
    (limit : Nat := 20) : Array Name :=
  pattern.collect index.entries.size (fun id => id.toUInt32)
    (fun id => index.entries[id.toNat]?) (·.name) limit |>.map (·.name)

def search (index : Index) (pattern : SearchPattern)
    (limit : Nat := 20) : Array Name :=
  match pattern.candidatePlan.select (index.trigrams.find? · |>.map (·.size)) with
  | none => index.searchAll pattern limit
  | some grams =>
    let ids := Id.run <| SearchPattern.mergePostingsM grams fun gram =>
      pure ((index.trigrams.find? gram).getD #[])
    pattern.collect ids.size (fun id => ids[id]!)
      (fun id => index.entries[id.toNat]?) (·.name) limit |>.map (·.name)

private def related (index : Index) (name : Name) (upstream : Bool)
    (limit : Nat) : Array Name :=
  match index.findId? name with
  | some id =>
    (index.relatedIds id upstream limit).map fun id => index.entries[id.toNat]!.name
  | none => #[]

def upstream (index : Index) (name : Name) (limit : Nat) : Array Name :=
  index.related name true limit

def downstream (index : Index) (name : Name) (limit : Nat) : Array Name :=
  index.related name false limit

def moduleOf? (index : Index) (name : Name) : Option Name :=
  index.findId? name |>.map fun id => index.entries[id.toNat]!.moduleName

end Index
end LeanReach
