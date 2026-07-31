import LeanReach.Cache.Codec
import LeanReach.Cache.Storage
import LeanReach.Search.Index
import LeanReach.Search.Pattern

namespace LeanReach.SearchCache

open Lean

private def shardCount := 256

structure Table where
  names : Array Name
  owners : Array UInt32
  modules : Array Name
  forwardCounts : Array UInt32
  reverseCounts : Array UInt32

def Table.ofIndex (index : Index) : Table := Id.run do
  let (entries, _) := index.catalog
  let (reverseCounts, forwardCounts) := index.relationCountsById
  let mut moduleIds : NameMap UInt32 := {}
  let mut modules := #[]
  let mut names := #[]
  let mut owners := #[]
  for entry in entries do
    let owner ← match moduleIds.find? entry.moduleName with
      | some owner => pure owner
      | none =>
        let owner := modules.size.toUInt32
        moduleIds := moduleIds.insert entry.moduleName owner
        modules := modules.push entry.moduleName
        pure owner
    names := names.push entry.name
    owners := owners.push owner
  return { names, owners, modules, forwardCounts, reverseCounts }

def Table.isValid (table : Table) : Bool :=
  table.names.size == table.owners.size &&
    table.names.size == table.forwardCounts.size &&
    table.names.size == table.reverseCounts.size &&
    table.owners.all (·.toNat < table.modules.size)

def Table.size (table : Table) : Nat :=
  table.names.size

def Table.locatedAt? (table : Table) (id : UInt32) : Option LocatedName := do
  let name ← table.names[id.toNat]?
  let owner ← table.owners[id.toNat]?
  let moduleName ← table.modules[owner.toNat]?
  return { name, moduleName }

def Table.locatedAt! (table : Table) (id : UInt32) : LocatedName :=
  table.locatedAt? id |>.get!

private def Table.findId? (table : Table) (name : Name) : Option UInt32 :=
  NameSearch.findSorted? table.size (table.names[·]!) name |>.map (·.toUInt32)

def Table.located? (table : Table) (name : Name) : Option LocatedName :=
  table.findId? name >>= table.locatedAt?

def Table.relationCounts (table : Table) (name : Name) : Nat × Nat :=
  match table.findId? name with
  | some id =>
    (table.reverseCounts[id.toNat]?.map (·.toNat) |>.getD 0,
      table.forwardCounts[id.toNat]?.map (·.toNat) |>.getD 0)
  | none => (0, 0)

def Table.moduleOf? (table : Table) (name : Name) : Option Name :=
  table.located? name |>.map (·.moduleName)

def Table.declarationsByModule (table : Table) : NameMap (Array Name) := Id.run do
  let mut declarations : NameMap (Array Name) := {}
  for id in [0:table.size] do
    let entry := table.locatedAt! id.toUInt32
    declarations := declarations.alter entry.moduleName fun names =>
      some ((names.getD #[]).push entry.name)
  return declarations

private structure View where
  roots : Array Name
  olean : System.FilePath
  depHash : String
  table : IO.Ref (Option Table)
  directory : IO.Ref (Option (Data.Trie UInt32))
  postings : IO.Ref (Array (Option (Data.Trie ByteArray)))

private initialize viewCache : IO.Ref (Std.HashMap String View) ← IO.mkRef {}

private def stem (roots : Array Name) :=
  if roots.size == 1 then "leanreach-search" else "leanreach-roots-search"

private def path (roots : Array Name) (olean : System.FilePath) (part : String) :=
  -- Search cache format 6.
  olean.withExtension s!"{stem roots}-6-{part}"

private def markerPath (roots : Array Name) (olean : System.FilePath) :=
  path roots olean "root"

private def shardPath (roots : Array Name) (olean : System.FilePath) (id : Nat) :=
  path roots olean s!"posting-{id}"

private def shard (trigram : String) : Nat :=
  (hash trigram % UInt64.ofNat shardCount).toNat

private def loadView (roots : Array Name) (olean : System.FilePath)
    (depHash : String) : IO View := do
  let key := Cache.loadedKey (markerPath roots olean) depHash
  if let some view := (← viewCache.get).get? key then return view
  let view := {
    roots, olean, depHash
    table := ← IO.mkRef none
    directory := ← IO.mkRef none
    postings := ← IO.mkRef (Array.replicate shardCount none)
  }
  viewCache.modify (·.insert key view)
  return view

private def memoize {α : Type} (slot : IO.Ref (Option α))
    (action : IO (Option α)) : IO (Option α) := do
  if let some value ← slot.get then return some value
  let some value ← action | return none
  slot.set (some value)
  return some value

private unsafe def loadViewTable (view : View) : IO (Option Table) :=
  memoize view.table <| do
    let table? ← unsafe Cache.loadPart Table
      (path view.roots view.olean "table") view.depHash
    return table?.filter (·.isValid)

private unsafe def loadPostings (view : View) (id : Nat) :
    IO (Option (Data.Trie ByteArray)) := do
  if let some postings := (← view.postings.get)[id]! then return some postings
  let some postings ← unsafe Cache.loadPart (Data.Trie ByteArray)
      (shardPath view.roots view.olean id) view.depHash | return none
  view.postings.modify (·.set! id (some postings))
  return some postings

private def ready (roots : Array Name) (olean : System.FilePath)
    (depHash : String) : IO Bool :=
  Cache.markerMatches (markerPath roots olean) depHash

unsafe def isBuilt (roots : Array Name) : IO Bool := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  ready roots olean depHash

unsafe def loadTable (roots : Array Name) : IO (Option Table) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unless ← ready roots olean depHash do return none
  unsafe loadViewTable (← loadView roots olean depHash)

private partial def collectPostings (trie : Data.Trie (Array UInt32)) :
    Data.Trie UInt32 × Array (Data.Trie ByteArray) :=
  (visit ByteArray.empty trie).run ({}, Array.replicate shardCount {}) |>.2
where
  add (keyBytes : ByteArray) (value : Option (Array UInt32)) :
      StateM (Data.Trie UInt32 × Array (Data.Trie ByteArray)) Unit := do
    if let some ids := value then
      let trigram := String.fromUTF8! keyBytes
      modify fun (directory, shards) =>
        (directory.insert trigram ids.size.toUInt32,
          shards.modify (shard trigram)
            (·.insert trigram (Cache.Codec.packDeltas ids)))

  visit (keyBytes : ByteArray) :
      Data.Trie (Array UInt32) →
        StateM (Data.Trie UInt32 × Array (Data.Trie ByteArray)) Unit
    | .leaf value => add keyBytes value
    | .node1 value byte child => do
      add keyBytes value
      visit (keyBytes.push byte) child
    | .node value bytes children => do
      add keyBytes value
      for i in [0:children.size] do
        visit (keyBytes.push bytes[i]!) children[i]!

unsafe def build (roots : Array Name) (index : Index) : IO Nat := do
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  if ← ready roots olean depHash then return 0
  let (entries, trigrams) := index.catalog
  let table := Table.ofIndex index
  let (directory, shards) := collectPostings trigrams
  Cache.savePart (path roots olean "table") depHash table
    (Name.str root "_leanreachSearchTable")
  Cache.savePart (path roots olean "directory") depHash directory
    (Name.str root "_leanreachSearchDirectory")
  let mut offset := 0
  while offset < shardCount do
    let stop := min shardCount (offset + 16)
    let tasks ← (Array.range (stop - offset)).mapM fun delta =>
      let id := offset + delta
      IO.asTask <| Cache.savePart (shardPath roots olean id) depHash
        shards[id]! (Name.str root s!"_leanreachSearchPosting{id}")
    tasks.forM fun task => IO.ofExcept task.get
    offset := stop
  IO.FS.writeFile (markerPath roots olean) depHash
  return entries.size

unsafe def search (roots : Array Name) (pattern : SearchPattern)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unless ← ready roots olean depHash do return none
  if limit == 0 then return some #[]
  let view ← loadView roots olean depHash
  let findAll := do
    let some table ← unsafe loadViewTable view | return none
    return some (pattern.collect table.size (fun id => id.toUInt32)
      table.locatedAt? (·.name) limit)
  match pattern.candidatePlan with
  | .all => findAll
  | .empty => return some #[]
  | plan@(.postings _) =>
    let some directory ← memoize view.directory <|
        unsafe Cache.loadPart (Data.Trie UInt32)
          (path view.roots view.olean "directory") view.depHash |
      return none
    match plan.select (directory.find? · |>.map (·.toNat)) with
    | .empty => return some #[]
    | .all => findAll
    | .postings alternatives =>
      let mut ids := #[]
      for grams in alternatives do
        let some gram := grams[0]? | continue
        let some postings ← unsafe loadPostings view (shard gram) | return none
        let candidates :=
          (postings.find? gram >>= Cache.Codec.unpackDeltas).getD #[]
        ids := SearchPattern.mergeSortedIds ids candidates
      if ids.isEmpty then return some #[]
      let some table ← unsafe loadViewTable view | return none
      return some (pattern.collect ids.size (fun id => ids[id]!)
        table.locatedAt? (·.name) limit)

end LeanReach.SearchCache
