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
  olean.withExtension "leanreach-query-overlay-catalog-2"

private def relationsPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension "leanreach-query-overlay-relations-3"

private initialize loadedCatalogs : IO.Ref (Std.HashMap String Catalog) ← IO.mkRef {}
private initialize loadedRelations : IO.Ref (Std.HashMap String Relations) ← IO.mkRef {}

private unsafe def loadCached {α : Type} (roots : Array Name)
    (pathOf : System.FilePath → System.FilePath)
    (loaded : IO.Ref (Std.HashMap String α)) : IO (Option α) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  let path := pathOf olean
  let key := Cache.loadedKey path depHash
  if let some value := (← loaded.get).get? key then return some value
  let some value ← unsafe Cache.loadPart α path depHash | return none
  loaded.modify (·.insert key value)
  return some value

unsafe def loadCatalog (roots : Array Name) : IO (Option Catalog) :=
  unsafe loadCached roots catalogPath loadedCatalogs

unsafe def loadRelations (roots : Array Name) : IO (Option Relations) :=
  unsafe loadCached roots relationsPath loadedRelations

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
  let localNames := targets.toArray.map (·.2) |>.qsort fun left right =>
    Name.lt left.name right.name
  return { baseRoot, localNames }

unsafe def buildRelations (roots : Array Name) (baseRoot : Name)
    (baseModules : Array Name) : IO Relations := do
  let mut entries : NameMap Entry := {}
  for (moduleName, declarations) in ← unsafe Cache.moduleClosure roots
      (excludedModules baseRoot baseModules) do
    for (name, dependencies) in declarations do
      let target := { name, moduleName }
      entries := entries.alter name fun previous => some {
        target
        dependencies :=
          ((previous.map (·.dependencies)).getD {} ++
            NameSet.ofArray dependencies).erase name
      }
  let mut reverse : NameMap (Array LocatedName) := {}
  for (_, entry) in entries do
    for dependency in entry.dependencies do
      reverse := reverse.alter dependency fun targets =>
        some ((targets.getD #[]).push entry.target)
  return { baseRoot, entries, reverse }

def Relations.catalog (relations : Relations) : Catalog := {
  baseRoot := relations.baseRoot
  localNames := relations.entries.toArray.map (·.2.target) |>.qsort fun left right =>
    Name.lt left.name right.name
}

private unsafe def saveCached {α : Type} (roots : Array Name) (value : α)
    (pathOf : System.FilePath → System.FilePath) (suffix : String)
    (loaded : IO.Ref (Std.HashMap String α)) : IO Unit := do
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  let path := pathOf olean
  Cache.savePart path depHash value (Name.str root suffix)
  loaded.modify (·.insert (Cache.loadedKey path depHash) value)

unsafe def saveCatalog (roots : Array Name) (catalog : Catalog) : IO Unit :=
  unsafe saveCached roots catalog catalogPath
    "_leanreachQueryOverlayCatalog" loadedCatalogs

unsafe def saveRelations (roots : Array Name) (relations : Relations) : IO Unit :=
  unsafe saveCached roots relations relationsPath
    "_leanreachQueryOverlayRelations" loadedRelations

end LeanReach.QueryOverlay
