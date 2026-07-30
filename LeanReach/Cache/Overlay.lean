import LeanReach.Cache.Index
import LeanReach.Search.Rank

namespace LeanReach.QueryOverlay

open Lean

structure Entry where
  target : LocatedName
  dependencies : Array Name

structure Data where
  baseRoot : Name
  entries : NameMap Entry
  reverse : NameMap (Array LocatedName)
  queries : NameMap CachedQuery

private def path (olean : System.FilePath) : System.FilePath :=
  -- Overlay cache format 6.
  olean.withExtension "leanreach-query-overlay-6"

unsafe def load (roots : Array Name) : IO (Option Data) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unsafe Cache.loadPart Data (path olean) depHash

def Data.size (data : Data) : Nat :=
  data.entries.size

def Data.local? (data : Data) (name : Name) : Option LocatedName :=
  data.entries.find? name |>.map (·.target)

def Data.localNames (data : Data) : Array LocatedName :=
  data.entries.foldl (init := #[]) fun result _ entry => result.push entry.target

def Data.cached? (data : Data) (name : Name) : Option CachedQuery :=
  data.queries.find? name

def Data.affectedNames (data : Data) : Array Name := Id.run do
  let mut affected : NameSet := {}
  for (name, entry) in data.entries do
    affected := affected.insert name
    for dependency in entry.dependencies do
      affected := affected.insert dependency
  let mut names := #[]
  for name in affected do names := names.push name
  return names

private def Data.moduleOf? (data : Data) (base : Index) (name : Name) :
    Option LocatedName :=
  data.local? name <|> base.located? name

def Data.queryFromBase (data : Data) (base : Index) (target : LocatedName)
    (cached? : Option CachedQuery) : CachedQuery :=
  let upstream :=
    match data.entries.find? target.name with
    | some entry => entry.dependencies.filterMap (data.moduleOf? base)
    | none => cached?.map (·.upstream) |>.getD #[]
  let downstream :=
    (cached?.map (·.downstream) |>.getD #[]) ++
      (data.reverse.find? target.name).getD #[]
  -- Keep base priors stable so the overlay only changes directly affected neighborhoods.
  let reverseCount name := base.reverseCount name +
    if data.entries.contains name then
      data.reverse.find? name |>.map (·.size) |>.getD 0
    else 0
  let forwardCount name :=
    data.entries.find? name |>.map (·.dependencies.size) |>.getD (base.forwardCount name)
  let rank upstream candidates :=
    Rank.select target candidates id
      (fun candidate => Rank.prior base.size
        (reverseCount candidate.name) (forwardCount candidate.name) upstream)
      cachedQueryLimit
  {
    target
    upstream := rank true upstream
    downstream := rank false downstream
  }

unsafe def buildGraph (roots : Array Name) (baseRoot : Name) : IO Data := do
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
  return { baseRoot, entries, reverse, queries := {} }

unsafe def save (roots : Array Name) (data : Data) : IO Unit := do
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  Cache.pickle (path olean) (depHash, data) (Name.str root "_leanreachQueryOverlay")

end LeanReach.QueryOverlay
