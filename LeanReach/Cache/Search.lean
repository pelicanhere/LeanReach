import LeanReach.Cache.Storage
import LeanReach.Search.Index
import LeanReach.Search.Resolve

namespace LeanReach.SearchCache

open Lean

private def shardCount := 256

private abbrev NameTable := Array Name × Array UInt32 × Array Name

private structure View where
  roots : Array Name
  olean : System.FilePath
  depHash : String
  table : IO.Ref (Option NameTable)
  directory : IO.Ref (Option (Data.Trie UInt32))
  postings : IO.Ref (Array (Option (Data.Trie ByteArray)))

private initialize viewCache : IO.Ref (Std.HashMap String View) ← IO.mkRef {}

private def stem (roots : Array Name) :=
  if roots.size == 1 then "leanreach-search" else "leanreach-roots-search"

private def path (roots : Array Name) (olean : System.FilePath) (part : String) :=
  -- Search cache format 4.
  olean.withExtension s!"{stem roots}-4-{part}"

private def markerPath (roots : Array Name) (olean : System.FilePath) :=
  path roots olean "root"

private def shardPath (roots : Array Name) (olean : System.FilePath) (id : Nat) :=
  path roots olean s!"posting-{id}"

private def shard (trigram : String) : Nat :=
  (hash trigram % UInt64.ofNat shardCount).toNat

private def viewKey (roots : Array Name) (olean : System.FilePath)
    (depHash : String) : String :=
  s!"{markerPath roots olean}\u0000{depHash}"

private def loadView (roots : Array Name) (olean : System.FilePath)
    (depHash : String) : IO View := do
  let key := viewKey roots olean depHash
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

private unsafe def loadTable (view : View) : IO (Option NameTable) :=
  memoize view.table <| unsafe Cache.loadPart NameTable
    (path view.roots view.olean "names") view.depHash

private unsafe def loadDirectory (view : View) :
    IO (Option (Data.Trie UInt32)) :=
  memoize view.directory <| unsafe Cache.loadPart (Data.Trie UInt32)
    (path view.roots view.olean "directory") view.depHash

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

private def packIds (ids : Array UInt32) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  let mut previous := 0
  for id in ids do
    let current := id.toNat
    let mut delta := current - previous
    while delta ≥ 128 do
      bytes := bytes.push (UInt8.ofNat (delta % 128 + 128))
      delta := delta / 128
    bytes := bytes.push (UInt8.ofNat delta)
    previous := current
  return bytes

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
          shards.modify (shard trigram) (·.insert trigram (packIds ids)))

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

private def unpackIds (bytes : ByteArray) : Array UInt32 := Id.run do
  let mut ids := #[]
  let mut previous := 0
  let mut delta := 0
  let mut scale := 1
  for byte in bytes do
    let value := byte.toNat
    delta := delta + value % 128 * scale
    if value < 128 then
      previous := previous + delta
      ids := ids.push previous.toUInt32
      delta := 0
      scale := 1
    else
      scale := scale * 128
  return ids

private def makeNameTable (entries : Array LocatedName) : NameTable := Id.run do
  let mut ids : NameMap UInt32 := {}
  let mut modules := #[]
  let mut names := #[]
  let mut owners := #[]
  for entry in entries do
    let id ← match ids.find? entry.moduleName with
      | some id => pure id
      | none =>
        let id := modules.size.toUInt32
        ids := ids.insert entry.moduleName id
        modules := modules.push entry.moduleName
        pure id
    names := names.push entry.name
    owners := owners.push id
  return (names, owners, modules)

unsafe def build (roots : Array Name) (index : Index) : IO Nat := do
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  if ← ready roots olean depHash then return 0
  let (entries, trigrams) := index.catalog
  let (directory, shards) := collectPostings trigrams
  Cache.savePart (path roots olean "names") depHash (makeNameTable entries)
    (Name.str root "_leanreachSearchNames")
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

private def findMatches (table : NameTable) (size : Nat) (idAt : Nat → UInt32)
    (query : String) (limit : Nat) : Array LocatedName :=
  let (names, owners, modules) := table
  let located? id := do
    let name ← names[id.toNat]?
    let owner ← owners[id.toNat]?
    let moduleName ← modules[owner.toNat]?
    return { name, moduleName }
  NameResolve.collect query size idAt located? (·.name) limit

unsafe def lookup (roots : Array Name) (query : String)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unless ← ready roots olean depHash do return none
  let view ← loadView roots olean depHash
  let query := query.toLower
  if query.length < 3 then
    let some table ← unsafe loadTable view | return none
    return some (findMatches table table.1.size (fun id => id.toUInt32) query limit)
  let some directory ← unsafe loadDirectory view | return none
  let some trigram := NameSearch.rarestTrigram? (NameSearch.trigrams query)
      (directory.find? · |>.map (·.toNat)) | return some #[]
  let some postings ← unsafe loadPostings view (shard trigram) | return none
  let ids := (postings.find? trigram).map unpackIds |>.getD #[]
  if ids.isEmpty then return some #[]
  let some table ← unsafe loadTable view | return none
  return some (findMatches table ids.size (fun id => ids[id]!) query limit)

end LeanReach.SearchCache
