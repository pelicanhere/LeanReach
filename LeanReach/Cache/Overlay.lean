import LeanReach.Cache.Index
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

private def catalogPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension "leanreach-query-overlay-catalog-1"

private def relationsPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension "leanreach-query-overlay-relations-2"

private initialize loadedCatalogs : IO.Ref (Std.HashMap String Catalog) ← IO.mkRef {}
private initialize loadedRelations : IO.Ref (Std.HashMap String Relations) ← IO.mkRef {}

private def loadedKey (path : System.FilePath) (depHash : String) : String :=
  s!"{path}\u0000{depHash}"

unsafe def loadCatalog (roots : Array Name) : IO (Option Catalog) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  let path := catalogPath olean
  let key := loadedKey path depHash
  if let some catalog := (← loadedCatalogs.get).get? key then return some catalog
  let some catalog ← unsafe Cache.loadPart Catalog path depHash | return none
  loadedCatalogs.modify (·.insert key catalog)
  return some catalog

unsafe def loadRelations (roots : Array Name) : IO (Option Relations) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  let path := relationsPath olean
  let key := loadedKey path depHash
  if let some relations := (← loadedRelations.get).get? key then return some relations
  let some relations ← unsafe Cache.loadPart Relations path depHash | return none
  loadedRelations.modify (·.insert key relations)
  return some relations

def Relations.local? (data : Relations) (name : Name) : Option LocatedName :=
  data.entries.find? name |>.map (·.target)

def Relations.affects (data : Relations) (name : Name) : Bool :=
  data.entries.contains name || data.reverse.contains name

private def Relations.moduleOf? (data : Relations) (base : BaseMetadata) (name : Name) :
    Option LocatedName :=
  data.local? name <|> base.located? name

def Relations.queryFromBase (data : Relations) (base : BaseMetadata) (target : LocatedName)
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

private def excludedModules (baseRoot : Name) (baseModules : Array Name) : NameHashSet :=
  (baseModules.foldl (init := ({} : NameHashSet)) (·.insert ·)).insert baseRoot

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
          ((previous.map (·.dependencies)).getD {} ++ dependencies).erase name
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

unsafe def saveCatalog (roots : Array Name) (catalog : Catalog) : IO Unit := do
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  let path := catalogPath olean
  Cache.savePart path depHash catalog (Name.str root "_leanreachQueryOverlayCatalog")
  loadedCatalogs.modify (·.insert (loadedKey path depHash) catalog)

unsafe def saveRelations (roots : Array Name) (relations : Relations) : IO Unit := do
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  let path := relationsPath olean
  Cache.savePart path depHash relations (Name.str root "_leanreachQueryOverlayRelations")
  loadedRelations.modify (·.insert (loadedKey path depHash) relations)

end LeanReach.QueryOverlay
