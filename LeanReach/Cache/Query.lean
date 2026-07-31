import LeanReach.Cache.Index
import LeanReach.Cache.Codec
import LeanReach.Cache.OverlayDelta
import LeanReach.Cache.Search
import LeanReach.Search.Match

namespace LeanReach.QueryCache

open Lean

private def shardCount := 1024
private def rankedPrefixLimit := 10

private def shard (name : Name) : Nat :=
  (hash ((NameSearch.leaf? name).getD "").toLower %
    UInt64.ofNat shardCount).toNat

private def shardPath (olean : System.FilePath) (id : Nat) : System.FilePath :=
  -- Query-shard format 17.
  olean.withExtension s!"leanreach-query-17-{id}"

private def markerPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension "leanreach-query-root-17"

private def ready (olean : System.FilePath) (depHash : String) : IO Bool :=
  Cache.markerMatches (markerPath olean) depHash

private def header (depHash : String) : ByteArray :=
  Cache.Codec.pushBytes ByteArray.empty depHash.toUTF8

private def prioritize (index : Index) (source : UInt32)
    (ids : Array UInt32) (upstream : Bool) : Array UInt32 :=
  let head := index.relatedIds source upstream rankedPrefixLimit
  if head.size == ids.size then head
  else head ++ ids.filter (!head.contains ·)

private def buildShards (index : Index) (start stop : Nat) :
    Array ByteArray := Id.run do
  let entries := index.catalog.1
  let mut shards := Array.replicate shardCount ByteArray.empty
  for id in [start:stop] do
    let target := entries[id]!
    let source := id.toUInt32
    shards := shards.modify (shard target.name) fun bytes =>
      Cache.Codec.pushArray (Cache.Codec.pushArray
        (Cache.Codec.pushUInt32 bytes id.toUInt32)
        (prioritize index source index.forward[id]! true))
        (prioritize index source index.reverse[id]! false)
  return shards

private unsafe def isFullBuilt (roots : Array Name) : IO Bool := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  ready olean depHash

private unsafe def buildFull (roots : Array Name) (index : Index) : IO Nat := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  if ← ready olean depHash then return 0
  let mut jobs := #[]
  let chunk := (index.size + 3) / 4
  for worker in [0:4] do
    let start := worker * chunk
    let stop := min index.size (start + chunk)
    if start < stop then
      jobs := jobs.push (← IO.asTask <| IO.lazyPure fun _ =>
        buildShards index start stop)
  let mut shards := Array.replicate shardCount (header depHash)
  for job in jobs do
    let part ← IO.ofExcept job.get
    for id in [0:shardCount] do
      shards := shards.modify id (· ++ part[id]!)
  let mut offset := 0
  while offset < shardCount do
    let stop := min shardCount (offset + 16)
    let tasks ← (Array.range (stop - offset)).mapM fun delta =>
      let id := offset + delta
      IO.asTask <| Cache.saveBytes (shardPath olean id) shards[id]!
    tasks.forM fun task => IO.ofExcept task.get
    offset := stop
  IO.FS.writeFile (markerPath olean) depHash
  return index.size

private unsafe def fullCachesBuilt (roots : Array Name) : IO Bool :=
  return (← unsafe isFullBuilt roots) &&
    (← unsafe SearchCache.isBuilt roots)

private unsafe def buildFullCaches (roots : Array Name) : IO Nat := do
  let queryReady ← unsafe isFullBuilt roots
  let searchReady ← unsafe SearchCache.isBuilt roots
  if queryReady && searchReady then return 0
  let index ← unsafe Cache.materializeIndex roots
  let searchCount ←
    if searchReady then pure 0 else unsafe SearchCache.build roots index
  let queryCount ← if queryReady then pure 0 else unsafe buildFull roots index
  return max queryCount searchCount

private unsafe def baseRoot? (roots : Array Name) : IO (Option Name) := do
  if roots.size < 2 then return none
  if roots.contains `Mathlib then return some `Mathlib
  for root in roots do
    if ← unsafe fullCachesBuilt #[root] then return some root
  return none

private unsafe def readCatalog (roots : Array Name) :
    IO (Option QueryOverlay.Catalog) := do
  if roots.size ≤ 1 then return none
  if let some catalog ← unsafe QueryOverlay.loadCatalog roots then
    return some catalog
  unsafe QueryOverlay.Incremental.loadCatalog roots

unsafe def isBuilt (roots : Array Name) : IO Bool := do
  if roots.size == 1 then return ← unsafe fullCachesBuilt roots
  let some catalog ← unsafe readCatalog roots | return false
  let some relations ← unsafe QueryOverlay.Incremental.loadRelations roots | return false
  return (← unsafe fullCachesBuilt #[catalog.baseRoot]) &&
    relations.baseRoot == catalog.baseRoot

private unsafe def loadCatalog (roots : Array Name) :
    IO (Option QueryOverlay.Catalog) := do
  if let some catalog ← unsafe readCatalog roots then return some catalog
  let some baseRoot ← unsafe baseRoot? roots | return none
  unless ← unsafe fullCachesBuilt #[baseRoot] do return none
  let some table ← unsafe SearchCache.loadTable #[baseRoot] | return none
  let catalog ← unsafe QueryOverlay.buildCatalog roots baseRoot table.modules
  unsafe QueryOverlay.saveCatalog roots catalog
  return some catalog

private unsafe def loadRelations (roots : Array Name) (baseRoot : Name) :
    IO QueryOverlay.Relations := do
  if let some relations ← unsafe QueryOverlay.Incremental.loadRelations roots then
    if relations.baseRoot == baseRoot then return relations
  let some table ← unsafe SearchCache.loadTable #[baseRoot] |
    throw <| IO.userError s!"declaration table for '{baseRoot}' is unavailable"
  let (relations, fragments) ←
    unsafe QueryOverlay.buildRelationsWithFragments roots baseRoot table.modules
  unsafe QueryOverlay.Incremental.saveBaseline roots
    relations fragments
  return relations

unsafe def build (roots : Array Name) : IO Nat := do
  if roots.size == 1 then return ← unsafe buildFullCaches roots
  let catalog? ← unsafe readCatalog roots
  let baseRoot? ← match catalog? with
    | some catalog => pure (some catalog.baseRoot)
    | none => unsafe baseRoot? roots
  let some baseRoot := baseRoot? | return ← unsafe buildFullCaches roots
  let count ← unsafe buildFullCaches #[baseRoot]
  let relations ← unsafe loadRelations roots baseRoot
  if catalog?.isNone then
    unsafe QueryOverlay.saveCatalog roots relations.catalog
  return max relations.entries.size count

private unsafe def loadShard (roots : Array Name) (name : Name) :
    IO (Option (ByteArray × String)) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unless ← ready olean depHash do return none
  try return some (← IO.FS.readBinFile (shardPath olean (shard name)), depHash)
  catch _ => return none

private def readIds (bytes : ByteArray) (count total keep : Nat) :
    Cache.Codec.Decoder (Array UInt32) := do
  guard (count ≤ total)
  let keep := min count keep
  let mut ids := Array.mkEmpty keep
  for index in [0:count] do
    let id ← Cache.Codec.Decoder.readUInt32 bytes
    guard (id.toNat < total)
    if index < keep then ids := ids.push id
  return ids

private def mergeResults {α : Type} (nameOf : α → Name)
    (localResults baseResults : Array α) (limit : Nat) : Array α := Id.run do
  let byName : NameMap α := ({} : NameMap α)
    |>.insertMany (baseResults.map fun item => (nameOf item, item))
    |>.insertMany (localResults.map fun item => (nameOf item, item))
  return (byName.valuesArray.qsort fun left right =>
    Name.lt (nameOf left) (nameOf right)).take limit

private def queryFromEdges (table : SearchCache.Table) (targetId : UInt32)
    (upstreamIds downstreamIds : Array UInt32) (limits : Limits) : CachedQuery :=
  let target := table.locatedAt! targetId
  let rank (ids : Array UInt32) (upstream : Bool) (limit : Nat) :=
    let selected :=
      if limit ≤ rankedPrefixLimit then ids
      else
        Rank.select target ids table.locatedAt!
          (fun id =>
            Rank.prior table.size table.reverseCounts[id.toNat]!.toNat
              table.forwardCounts[id.toNat]!.toNat upstream)
          limit
    selected.map table.locatedAt!
  {
    target
    upstream := rank upstreamIds true limits.upstream
    downstream := rank downstreamIds false limits.downstream
  }

private unsafe def exactFull (roots : Array Name) (table : SearchCache.Table)
    (query : String) (limits : Limits) :
    IO (Option (Array CachedQuery)) := do
  let name := query.toName
  let some (bytes, depHash) ← unsafe loadShard roots name | return none
  let some (storedHash, afterHash) :=
      (Cache.Codec.Decoder.readBytes bytes).run 0 | return none
  unless storedHash == depHash.toUTF8 do return none
  let mut results := #[]
  let mut position := afterHash
  while position < bytes.size do
    let entry : Cache.Codec.Decoder
        (Bool × UInt32 × Array UInt32 × Array UInt32) := do
      let targetId ← Cache.Codec.Decoder.readUInt32 bytes
      let some target := table.locatedAt? targetId | failure
      let upstreamCount ← Cache.Codec.Decoder.readUInt32 bytes
      let matched := NameSearch.exactMatch name target.name
      let upstreamKeep :=
        if !matched then 0
        else if limits.upstream ≤ rankedPrefixLimit then limits.upstream
        else upstreamCount.toNat
      let upstream ← readIds bytes upstreamCount.toNat table.size upstreamKeep
      let downstreamCount ← Cache.Codec.Decoder.readUInt32 bytes
      let downstreamKeep :=
        if !matched then 0
        else if limits.downstream ≤ rankedPrefixLimit then limits.downstream
        else downstreamCount.toNat
      let downstream ← readIds bytes downstreamCount.toNat table.size downstreamKeep
      return (matched, targetId, upstream, downstream)
    let some ((matched, targetId, upstream, downstream), next) :=
        entry.run position | return none
    position := next
    if matched then
      results := results.push
        (queryFromEdges table targetId upstream downstream limits)
      if results.size == limits.search then break
  return some results

/-- Finds cached queries whose complete user names match case-sensitively. -/
unsafe def exactQueries (roots : Array Name) (query : String)
    (limits : Limits) : IO (Option (Array CachedQuery)) := do
  if limits.search == 0 then return some #[]
  let catalog? ← unsafe loadCatalog roots
  let some catalog := catalog? | do
    let some table ← unsafe SearchCache.loadTable roots | return none
    return ← unsafe exactFull roots table query limits
  let name := query.toName
  let localTargets := catalog.localNames.filter
    (NameSearch.exactMatch name ·.name) |>.take limits.search
  let some base ← unsafe SearchCache.loadTable #[catalog.baseRoot] | return none
  let some baseResults ← unsafe exactFull #[catalog.baseRoot] base query limits |
    return none
  if localTargets.isEmpty && baseResults.isEmpty then return some #[]
  let relations ← unsafe loadRelations roots catalog.baseRoot
  unless !localTargets.isEmpty ||
      baseResults.any (relations.affects ·.target.name) do
    return some baseResults
  let localResults := localTargets.map fun target =>
    relations.queryFromBase base target none limits
  let baseResults := baseResults.map fun cached =>
    if relations.affects cached.target.name then
      relations.queryFromBase base cached.target (some cached) limits
    else cached
  return some (mergeResults (·.target.name)
    localResults baseResults limits.search)

unsafe def search (roots : Array Name) (pattern : SearchPattern)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let catalog? ← unsafe loadCatalog roots
  let some catalog := catalog? | do
    return ← unsafe SearchCache.search roots pattern limit
  let some base ← unsafe SearchCache.search #[catalog.baseRoot] pattern limit |
    return none
  return some <| mergeResults (·.name)
    (pattern.collect catalog.localNames.size
      (fun id => catalog.localNames[id]!) some (·.name) limit)
    base limit

end LeanReach.QueryCache
