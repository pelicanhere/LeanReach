import LeanReach.Cache.Index
import LeanReach.Cache.Overlay
import LeanReach.Cache.Search
import LeanReach.Search.Match

namespace LeanReach.QueryCache

open Lean

private def shardCount := 1024

private def shard (name : Name) : Nat :=
  (hash ((NameSearch.leaf? name).getD "").toLower %
    UInt64.ofNat shardCount).toNat

private def shardPath (olean : System.FilePath) (id : Nat) : System.FilePath :=
  -- Query-shard format 10.
  olean.withExtension s!"leanreach-query-10-{id}"

private def markerPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension "leanreach-query-root-10"

private def baseMetadataPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension "leanreach-base-metadata-1"

private def baseMetadataMarkerPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension "leanreach-base-metadata-root-1"

private initialize loadedBaseMetadata :
    IO.Ref (Std.HashMap String QueryOverlay.BaseMetadata) ← IO.mkRef {}

private def baseMetadataKey (olean : System.FilePath) (depHash : String) : String :=
  s!"{baseMetadataPath olean}\u0000{depHash}"

private def ready (olean : System.FilePath) (depHash : String) : IO Bool :=
  Cache.markerMatches (markerPath olean) depHash

private def encodeShard (queries : Array CachedQuery) : String := Id.run do
  let mut ids : NameMap Nat := {}
  let mut modules := #[]
  for query in queries do
    for item in query.all do
      unless ids.contains item.moduleName do
        ids := ids.insert item.moduleName modules.size
        modules := modules.push item.moduleName
  let locatedFields (items : Array LocatedName) :=
    items.toList.flatMap fun item =>
      [item.name.toString, toString (ids.find? item.moduleName).get!]
  let encode (query : CachedQuery) :=
    String.intercalate "\t" <|
      [query.target.name.toString, toString (ids.find? query.target.moduleName).get!] ++
      locatedFields query.upstream ++ ["|"] ++ locatedFields query.downstream
  return String.intercalate "\n" <|
    modules.toList.map toString ++ ["|"] ++ queries.toList.map encode

private def decodeTarget (modules : Array Name) (name moduleId : String) :
    Option LocatedName := do
  let some moduleName := moduleId.toNat? >>= fun id => modules[id]? | none
  return { name := name.toName, moduleName }

private def target? (modules : Array Name) (line : String) : Option LocatedName := do
  let nameEnd ← line.find? '\t'
  let moduleStart := nameEnd.next!
  let moduleEnd ← moduleStart.find? '\t'
  decodeTarget modules
    (line.extract line.startPos nameEnd)
    (line.extract moduleStart moduleEnd)

private def decodeLocated (modules : Array Name) (fields : List String) :
    Option (Array LocatedName) :=
  go fields #[]
where
  go : List String → Array LocatedName → Option (Array LocatedName)
    | [], items => some items
    | name :: moduleId :: rest, items => do
      go rest (items.push (← decodeTarget modules name moduleId))
    | _, _ => none

private def decode (modules : Array Name) (line : String) : Option CachedQuery := do
  let name :: moduleId :: fields := line.splitOn "\t" | none
  let (upstream, downstream) := fields.span (· != "|")
  let _ :: downstream := downstream | none
  return {
    target := ← decodeTarget modules name moduleId
    upstream := ← decodeLocated modules upstream
    downstream := ← decodeLocated modules downstream
  }

private def readShard (path : System.FilePath) :
    IO (Option (Array Name × List String)) := do
  unless ← path.pathExists do return none
  try
    let (modules, lines) := (← IO.FS.readFile path).splitOn "\n" |>.span (· != "|")
    let _ :: lines := lines | return none
    return some (modules.toArray.map (·.toName), lines)
  catch _ => return none

private def buildShards (index : Index) (start stop : Nat) :
    Array (Array CachedQuery) := Id.run do
  let mut shards : Array (Array CachedQuery) := Array.replicate shardCount #[]
  for id in [start:stop] do
    let query := index.cachedQueryAt! id
    shards := shards.modify (shard query.target.name) (·.push query)
  return shards

private unsafe def isFullBuilt (roots : Array Name) : IO Bool := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  ready olean depHash

private unsafe def isBaseMetadataBuilt (roots : Array Name) : IO Bool := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  return (← Cache.markerMatches (baseMetadataMarkerPath olean) depHash) &&
    (← (baseMetadataPath olean).pathExists)

private unsafe def loadBaseMetadata (roots : Array Name) :
    IO (Option QueryOverlay.BaseMetadata) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unless ← Cache.markerMatches (baseMetadataMarkerPath olean) depHash do return none
  let key := baseMetadataKey olean depHash
  if let some base := (← loadedBaseMetadata.get).get? key then return some base
  let some base ← unsafe Cache.loadPart QueryOverlay.BaseMetadata
      (baseMetadataPath olean) depHash | return none
  unless base.isValid do return none
  loadedBaseMetadata.modify (·.insert key base)
  return some base

private unsafe def saveBaseMetadata (roots : Array Name)
    (base : QueryOverlay.BaseMetadata) : IO Unit := do
  let (olean, depHash, root) ← unsafe Cache.rootData roots
  loadedBaseMetadata.modify (·.insert (baseMetadataKey olean depHash) base)
  Cache.savePart (baseMetadataPath olean) depHash base
    (Name.str root "_leanreachBaseMetadata")
  IO.FS.writeFile (baseMetadataMarkerPath olean) depHash

private unsafe def ensureBaseMetadata (roots : Array Name) :
    IO QueryOverlay.BaseMetadata := do
  if let some base ← unsafe loadBaseMetadata roots then return base
  let base := QueryOverlay.BaseMetadata.ofIndex
    (← unsafe Cache.loadIndex roots true)
  try unsafe saveBaseMetadata roots base
  catch _ => IO.eprintln "leanreach: could not write base metadata cache"
  return base

private unsafe def baseRoot? (roots : Array Name) : IO (Option Name) := do
  if roots.size < 2 then return none
  if roots.contains `Mathlib then return some `Mathlib
  for root in roots do
    if ← unsafe isFullBuilt #[root] then return some root
  return none

private unsafe def readOverlay (roots : Array Name) : IO (Option QueryOverlay.Data) :=
  if roots.size > 1 then unsafe QueryOverlay.load roots else pure none

unsafe def isBuilt (roots : Array Name) : IO Bool := do
  if let some overlay ← unsafe readOverlay roots then
    return (← unsafe isFullBuilt #[overlay.baseRoot]) &&
      (← unsafe SearchCache.isBuilt #[overlay.baseRoot]) &&
      (← unsafe isBaseMetadataBuilt #[overlay.baseRoot])
  return (← unsafe isFullBuilt roots) &&
    (← unsafe SearchCache.isBuilt roots) &&
    (← unsafe isBaseMetadataBuilt roots)

private unsafe def buildFull (roots : Array Name) (index : Index) : IO Nat := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  if ← ready olean depHash then return 0
  let mut shards : Array (Array CachedQuery) := Array.replicate shardCount #[]
  let chunk := (index.size + 3) / 4
  let mut jobs := #[]
  for worker in [0:4] do
    let start := worker * chunk
    let stop := min index.size (start + chunk)
    if start < stop then
      jobs := jobs.push (← IO.asTask <| IO.lazyPure fun _ =>
        buildShards index start stop)
  for job in jobs do
    let part ← IO.ofExcept job.get
    for id in [0:shardCount] do
      shards := shards.modify id (· ++ part[id]!)
  let mut offset := 0
  while offset < shardCount do
    let stop := min shardCount (offset + 16)
    let tasks ← (Array.range (stop - offset)).mapM fun delta =>
      let id := offset + delta
      IO.asTask do
        let content ← IO.lazyPure fun _ => encodeShard shards[id]!
        IO.FS.writeFile (shardPath olean id) content
    tasks.forM fun task => IO.ofExcept task.get
    offset := stop
  IO.FS.writeFile (markerPath olean) depHash
  return index.size

private unsafe def buildFullCaches (roots : Array Name) : IO Nat := do
  let queryReady ← unsafe isFullBuilt roots
  let searchReady ← unsafe SearchCache.isBuilt roots
  let baseReady ← unsafe isBaseMetadataBuilt roots
  if queryReady && searchReady && baseReady then return 0
  let index ← unsafe Cache.loadIndex roots (!queryReady || !baseReady)
  let queryCount ← if queryReady then pure 0 else unsafe buildFull roots index
  let searchCount ←
    if searchReady then pure 0 else unsafe SearchCache.build roots index
  let baseCount ←
    if baseReady then pure 0
    else
      let base := QueryOverlay.BaseMetadata.ofIndex index
      unsafe saveBaseMetadata roots base
      pure base.entries.size
  return max queryCount (max searchCount baseCount)

private unsafe def buildOverlay (roots : Array Name) (baseRoot : Name) :
    IO QueryOverlay.Data := do
  let base ← unsafe ensureBaseMetadata #[baseRoot]
  let graph ← unsafe QueryOverlay.buildGraph roots baseRoot base.modules
  unsafe QueryOverlay.save roots graph
  return graph

private unsafe def loadOverlay (roots : Array Name) : IO (Option QueryOverlay.Data) := do
  if let some overlay ← unsafe readOverlay roots then return some overlay
  let some baseRoot ← unsafe baseRoot? roots | return none
  unless (← unsafe isFullBuilt #[baseRoot]) &&
      (← unsafe SearchCache.isBuilt #[baseRoot]) do return none
  return some (← unsafe buildOverlay roots baseRoot)

unsafe def build (roots : Array Name) : IO Nat := do
  if let some overlay ← unsafe readOverlay roots then
    return ← unsafe buildFullCaches #[overlay.baseRoot]
  if let some baseRoot ← unsafe baseRoot? roots then
    let count ← unsafe buildFullCaches #[baseRoot]
    let overlay ← unsafe buildOverlay roots baseRoot
    return max overlay.entries.size count
  unsafe buildFullCaches roots

private unsafe def loadShard (roots : Array Name) (name : Name) :
    IO (Option (Array Name × List String)) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unless ← ready olean depHash do return none
  readShard (shardPath olean (shard name))

private def localSearchMatches (overlay : QueryOverlay.Data)
    (pattern : SearchPattern) (limit : Nat) : Array LocatedName :=
  pattern.collect overlay.localNames.size (fun id => overlay.localNames[id]!)
    some (·.name) limit

private def mergeResults {α : Type} (nameOf : α → Name)
    (localResults baseResults : Array α) (limit : Nat) : Array α := Id.run do
  let mut byName : NameMap α := {}
  for item in baseResults do byName := byName.insert (nameOf item) item
  for item in localResults do byName := byName.insert (nameOf item) item
  let mut results := #[]
  for (_, item) in byName do results := results.push item
  return (results.qsort fun left right =>
    Name.lt (nameOf left) (nameOf right)).take limit

private unsafe def exactFull (roots : Array Name) (query : String)
    (limit : Nat) : IO (Option (Array CachedQuery)) := do
  let name := query.toName
  let some (modules, lines) ← unsafe loadShard roots name | return none
  let mut results := #[]
  for line in lines do
    let some target := target? modules line | continue
    if NameSearch.exactMatch name target.name then
      let some cached := decode modules line | return none
      results := results.push cached
      if results.size == limit then break
  return some results

/-- Finds cached queries whose complete user names match case-sensitively. -/
unsafe def exactQueries (roots : Array Name) (query : String)
    (limit : Nat) : IO (Option (Array CachedQuery)) := do
  if limit == 0 then return some #[]
  let overlay? ← unsafe loadOverlay roots
  let some overlay := overlay? | return ← unsafe exactFull roots query limit
  let name := query.toName
  let localTargets := overlay.localNames.filter
    (NameSearch.exactMatch name ·.name) |>.take limit
  let some baseResults ← unsafe exactFull #[overlay.baseRoot] query limit | return none
  unless !localTargets.isEmpty ||
      baseResults.any (overlay.affects ·.target.name) do
    return some baseResults
  let base ← unsafe ensureBaseMetadata #[overlay.baseRoot]
  let localResults := localTargets.map fun target =>
    overlay.queryFromBase base target none
  let baseResults := baseResults.map fun cached =>
    if overlay.affects cached.target.name then
      overlay.queryFromBase base cached.target (some cached)
    else cached
  return some (mergeResults (·.target.name) localResults baseResults limit)

unsafe def search (roots : Array Name) (pattern : SearchPattern)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let overlay? ← unsafe loadOverlay roots
  let some overlay := overlay? | do
    return ← unsafe SearchCache.search roots pattern limit
  let some base ← unsafe SearchCache.search #[overlay.baseRoot] pattern limit |
    return none
  return some <| mergeResults (·.name)
    (localSearchMatches overlay pattern limit) base limit

end LeanReach.QueryCache
