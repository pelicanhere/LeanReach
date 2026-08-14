import LeanReach.Cache.Index
import LeanReach.Cache.Search
import LeanReach.Search.Rank

namespace LeanReach.QueryOverlay

open Lean

structure Entry where
  target : LocatedName
  dependencies : NameSet

structure Catalog where
  baseRoot : Name
  localNames : Array LocatedName

structure Relations where
  baseRoot : Name
  entries : NameMap Entry
  reverse : NameMap (Array LocatedName)

private def catalogPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension "leanreach-query-overlay-catalog-6"

private initialize loadedCatalogs : IO.Ref (Std.HashMap String Catalog) ← IO.mkRef {}

unsafe def loadCatalog (roots : Array Name) : IO (Option Catalog) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  let path := catalogPath olean
  let key := Cache.loadedKey path depHash
  if let some catalog := (← loadedCatalogs.get).get? key then return some catalog
  let some catalog ← unsafe Cache.loadPart Catalog path depHash | return none
  loadedCatalogs.modify (·.insert key catalog)
  return some catalog

def Relations.affects (data : Relations) (name : Name) : Bool :=
  data.entries.contains name || data.reverse.contains name

private def Relations.moduleOf? (data : Relations) (base : SearchCache.Table)
    (name : Name) : Option LocatedName :=
  (data.entries.find? name |>.map (·.target)) <|> base.located? name

def Relations.queryFromBase (data : Relations) (base : SearchCache.Table)
    (target : LocatedName) (cached? : Option CachedQuery) (limits : Limits) :
    CachedQuery :=
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
      (if upstream then limits.upstream else limits.downstream)
  {
    target
    upstream := rank true upstream
    downstream := rank false downstream
  }

private def excludedModules (baseRoot : Name) (baseModules : Array Name) : NameHashSet :=
  (Std.HashSet.ofArray baseModules).insert baseRoot

unsafe def buildCatalog (roots : Array Name) (baseRoot : Name)
    (baseModules : Array Name) : IO Catalog := do
  let mut targets : NameMap LocatedName := {}
  for (moduleName, declarations) in ← unsafe Cache.moduleClosure roots
      (excludedModules baseRoot baseModules) do
    for (name, _) in declarations do
      targets := targets.insert name { name, moduleName }
  let localNames := LocatedName.sortByName targets.valuesArray
  return { baseRoot, localNames }

def relationsFromFragments (baseRoot : Name)
    (fragments : Array (Name × Cache.ModuleFragment)) : Relations := Id.run do
  let mut entries : NameMap Entry := {}
  for (moduleName, fragment) in fragments do
    for (name, dependencies) in fragment.declarations do
      let target := { name, moduleName }
      entries := entries.alter name fun previous => some {
        target
        dependencies :=
          ((previous.map (·.dependencies)).getD {} ++
            NameSet.ofArray dependencies.all).erase name
      }
  let mut reverse : NameMap (Array LocatedName) := {}
  for (_, entry) in entries do
    for dependency in entry.dependencies do
      reverse := reverse.alter dependency fun targets =>
        some ((targets.getD #[]).push entry.target)
  return { baseRoot, entries, reverse }

unsafe def buildRelationsWithFragments (roots : Array Name) (baseRoot : Name)
    (baseModules : Array Name) :
    IO (Relations × Array (Name × Cache.ModuleFragment)) := do
  let fragments ← unsafe Cache.moduleFragments roots
    (excludedModules baseRoot baseModules)
  return (relationsFromFragments baseRoot fragments, fragments)

def Relations.catalog (relations : Relations) : Catalog := {
  baseRoot := relations.baseRoot
  localNames := LocatedName.sortByName (relations.entries.valuesArray.map (·.target))
}

unsafe def saveCatalog (roots : Array Name) (catalog : Catalog) : IO Unit := do
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  let path := catalogPath olean
  Cache.savePart path depHash catalog (Name.str root "_leanreachQueryOverlayCatalog")
  loadedCatalogs.modify (·.insert (Cache.loadedKey path depHash) catalog)

end LeanReach.QueryOverlay
