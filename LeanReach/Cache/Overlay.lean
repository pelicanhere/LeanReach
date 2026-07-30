import LeanReach.Cache.Index
import LeanReach.Search.Rank

namespace LeanReach.QueryOverlay

open Lean

private def version := 5

structure Entry where
  target : LocatedName
  dependencies : Array Name

structure Data where
  baseRoot : Name
  entries : NameMap Entry
  reverse : NameMap (Array LocatedName)

private def path (olean : System.FilePath) : System.FilePath :=
  olean.withExtension s!"leanreach-query-overlay-{version}"

unsafe def load (roots : Array Name) : IO (Option Data) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unsafe Cache.loadPart Data (path olean) depHash

unsafe def build (roots : Array Name) (baseRoot : Name) : IO Data := do
  let mut entries : NameMap Entry := {}
  for moduleName in roots do
    unless moduleName == baseRoot do
      for (name, dependencies) in ← unsafe Cache.moduleDeclarations moduleName do
        let mut merged := entries.find? name |>.map (·.dependencies) |>.getD #[]
        for dependency in dependencies do
          if dependency != name && !merged.contains dependency then
            merged := merged.push dependency
        entries := entries.insert name { target := { name, moduleName }, dependencies := merged }
  let mut reverse : NameMap (Array LocatedName) := {}
  for (_, entry) in entries do
    for dependency in entry.dependencies do
      reverse := reverse.alter dependency fun targets =>
        some ((targets.getD #[]).push entry.target)
  let data : Data := { baseRoot, entries, reverse }
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  Cache.pickle (path olean) (depHash, data) (Name.str root "_leanreachQueryOverlay")
  return data

def Data.size (data : Data) : Nat :=
  data.entries.size

def Data.local? (data : Data) (name : Name) : Option LocatedName :=
  data.entries.find? name |>.map (·.target)

def Data.localNames (data : Data) : Array LocatedName :=
  data.entries.foldl (init := #[]) fun result _ entry => result.push entry.target

private def Data.moduleOf? (data : Data) (base : Index) (name : Name) :
    Option LocatedName :=
  data.local? name <|> base.located? name

def Data.query (data : Data) (base : Index) (target : LocatedName) : CachedQuery :=
  let upstream :=
    match data.entries.find? target.name with
    | some entry => entry.dependencies.filterMap (data.moduleOf? base)
    | none => base.relatedLocated target.name true
  let downstream :=
    base.relatedLocated target.name false ++
      (data.reverse.find? target.name).getD #[]
  let reverseCount name :=
    base.reverseCount name + (data.reverse.find? name |>.map (·.size) |>.getD 0)
  let forwardCount name :=
    data.entries.find? name |>.map (·.dependencies.size) |>.getD (base.forwardCount name)
  {
    target
    upstream := Rank.select target upstream id
      (fun candidate => Rank.prior (base.size + data.size)
        (reverseCount candidate.name) (forwardCount candidate.name) true)
      cachedQueryLimit
    downstream := Rank.select target downstream id
      (fun candidate => Rank.prior (base.size + data.size)
        (reverseCount candidate.name) (forwardCount candidate.name) false)
      cachedQueryLimit
  }

end LeanReach.QueryOverlay
