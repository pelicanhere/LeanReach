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
  queries : NameMap CachedQuery

private def path (olean : System.FilePath) : System.FilePath :=
  -- Overlay cache format 8.
  olean.withExtension "leanreach-query-overlay-8"

private initialize loadedCache : IO.Ref (Std.HashMap String Data) ← IO.mkRef {}

private def loadedKey (olean : System.FilePath) (depHash : String) : String :=
  s!"{path olean}\u0000{depHash}"

unsafe def load (roots : Array Name) : IO (Option Data) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  let key := loadedKey olean depHash
  if let some data := (← loadedCache.get).get? key then return some data
  let data? ← unsafe Cache.loadPart Data (path olean) depHash
  if let some data := data? then loadedCache.modify (·.insert key data)
  return data?

def Data.local? (data : Data) (name : Name) : Option LocatedName :=
  data.entries.find? name |>.map (·.target)

def Data.cached? (data : Data) (name : Name) : Option CachedQuery :=
  data.queries.find? name

def Data.affectedNames (data : Data) : Array Name := Id.run do
  let mut affected : NameSet := {}
  for (name, entry) in data.entries do
    affected := affected.insert name
    for dependency in entry.dependencies do
      affected := affected.insert dependency
  return affected.toArray

private def Data.moduleOf? (data : Data) (base : Index) (name : Name) :
    Option LocatedName :=
  data.local? name <|> base.located? name

def Data.queryFromBase (data : Data) (base : Index) (target : LocatedName)
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
        Rank.prior base.size reverseCount forwardCount upstream)
      cachedQueryLimit
  {
    target
    upstream := rank true upstream
    downstream := rank false downstream
  }

unsafe def buildGraph (roots : Array Name) (baseRoot : Name)
    (baseModules : Array Name) : IO Data := do
  let mut seen := baseModules.foldl
    (init := ({} : NameHashSet)) (·.insert ·)
  seen := seen.insert baseRoot
  let mut pending := roots
  let mut entries : NameMap Entry := {}
  while let some moduleName := pending.back? do
    pending := pending.pop
    if seen.contains moduleName then continue
    seen := seen.insert moduleName
    let (imports, declarations) ← unsafe Cache.moduleData moduleName
    for imported in imports do
      unless seen.contains imported do pending := pending.push imported
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
  return { baseRoot, entries, localNames, reverse, queries := {} }

unsafe def save (roots : Array Name) (data : Data) : IO Unit := do
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  Cache.savePart (path olean) depHash data (Name.str root "_leanreachQueryOverlay")
  loadedCache.modify (·.insert (loadedKey olean depHash) data)

end LeanReach.QueryOverlay
