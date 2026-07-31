import LeanReach.Cache.Index
import LeanReach.Search.Rank

namespace LeanReach.QueryOverlay

open Lean

structure Entry where
  target : LocatedName
  dependencies : NameSet

structure Data where
  baseRoot : Name
  entries : NameMap Entry
  localNames : Array LocatedName
  reverse : NameMap (Array LocatedName)

structure BaseMetadata where
  entries : Array LocatedName
  modules : Array Name
  reverseCounts : Array UInt32
  forwardCounts : Array UInt32

def BaseMetadata.ofIndex (index : Index) : BaseMetadata :=
  let (reverseCounts, forwardCounts) := index.relationCountsById
  {
    entries := index.catalog.1
    modules := index.modules
    reverseCounts
    forwardCounts
  }

def BaseMetadata.isValid (base : BaseMetadata) : Bool :=
  base.entries.size == base.reverseCounts.size &&
    base.entries.size == base.forwardCounts.size

private def BaseMetadata.findId? (base : BaseMetadata) (name : Name) : Option Nat :=
  NameSearch.findSorted? base.entries.size (base.entries[·]!.name) name

def BaseMetadata.located? (base : BaseMetadata) (name : Name) : Option LocatedName :=
  base.findId? name >>= fun id => base.entries[id]?

def BaseMetadata.relationCounts (base : BaseMetadata) (name : Name) : Nat × Nat :=
  match base.findId? name with
  | some id =>
    (base.reverseCounts[id]?.map (·.toNat) |>.getD 0,
      base.forwardCounts[id]?.map (·.toNat) |>.getD 0)
  | none => (0, 0)

private def path (olean : System.FilePath) : System.FilePath :=
  -- Overlay cache format 9.
  olean.withExtension "leanreach-query-overlay-9"

private initialize loadedCache : IO.Ref (Std.HashMap String Data) ← IO.mkRef {}

private def loadedKey (olean : System.FilePath) (depHash : String) : String :=
  s!"{path olean}\u0000{depHash}"

private def normalize (data : Data) : Data :=
  { data with
    localNames := data.localNames.qsort fun left right =>
      Name.lt left.name right.name }

unsafe def load (roots : Array Name) : IO (Option Data) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  let key := loadedKey olean depHash
  if let some data := (← loadedCache.get).get? key then return some data
  let some data ← unsafe Cache.loadPart Data (path olean) depHash | return none
  let data := normalize data
  loadedCache.modify (·.insert key data)
  return some data

def Data.local? (data : Data) (name : Name) : Option LocatedName :=
  data.entries.find? name |>.map (·.target)

def Data.affects (data : Data) (name : Name) : Bool :=
  data.entries.contains name || data.reverse.contains name

private def Data.moduleOf? (data : Data) (base : BaseMetadata) (name : Name) :
    Option LocatedName :=
  data.local? name <|> base.located? name

def Data.queryFromBase (data : Data) (base : BaseMetadata) (target : LocatedName)
    (cached? : Option CachedQuery) : CachedQuery :=
  let upstream :=
    match data.entries.find? target.name with
    | some entry => entry.dependencies.toArray.filterMap (data.moduleOf? base)
    | none => cached?.map (·.upstream) |>.getD #[]
  let downstream :=
    (cached?.map (·.downstream) |>.getD #[]) ++
      (data.reverse.find? target.name).getD #[]
  -- Keep base priors stable so the overlay only changes directly affected neighborhoods.
  let rank upstream candidates :=
    Rank.select target candidates id
      (fun candidate =>
        let (baseReverse, baseForward) := base.relationCounts candidate.name
        let reverseCount := baseReverse +
          ((data.reverse.find? candidate.name).map (·.size)).getD 0
        let forwardCount := data.entries.find? candidate.name
          |>.map (·.dependencies.size) |>.getD baseForward
        Rank.prior base.entries.size reverseCount forwardCount upstream)
      cachedQueryLimit
  {
    target
    upstream := rank true upstream
    downstream := rank false downstream
  }

unsafe def buildGraph (roots : Array Name) (baseRoot : Name)
    (baseModules : Array Name) : IO Data := do
  let mut excluded := baseModules.foldl
    (init := ({} : NameHashSet)) (·.insert ·)
  excluded := excluded.insert baseRoot
  let mut entries : NameMap Entry := {}
  for (moduleName, declarations) in ← unsafe Cache.moduleClosure roots excluded do
    for (name, dependencies) in declarations do
      entries := entries.alter name fun previous => some {
        target := { name, moduleName }
        dependencies :=
          ((previous.map (·.dependencies)).getD {} ++ dependencies).erase name
      }
  let mut reverse : NameMap (Array LocatedName) := {}
  let mut localNames := #[]
  for (_, entry) in entries do
    localNames := localNames.push entry.target
    for dependency in entry.dependencies do
      reverse := reverse.alter dependency fun targets =>
        some ((targets.getD #[]).push entry.target)
  return normalize { baseRoot, entries, localNames, reverse }

unsafe def save (roots : Array Name) (data : Data) : IO Unit := do
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  Cache.savePart (path olean) depHash data (Name.str root "_leanreachQueryOverlay")
  loadedCache.modify (·.insert (loadedKey olean depHash) data)

end LeanReach.QueryOverlay
