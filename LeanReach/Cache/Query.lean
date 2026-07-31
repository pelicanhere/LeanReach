import LeanReach.Cache.Index
import LeanReach.Cache.Overlay
import LeanReach.Cache.Search
import LeanReach.Search.Match
import LeanReach.Search.Resolve

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

private unsafe def loadQueries (roots : Array Name) (names : Array Name) :
    IO (NameMap CachedQuery) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unless ← ready olean depHash do return {}
  let mut wanted : NameHashSet := {}
  let mut shards := #[]
  let mut seenShards := Array.replicate shardCount false
  for name in names do
    wanted := wanted.insert name
    let id := shard name
    unless seenShards[id]! do
      seenShards := seenShards.set! id true
      shards := shards.push id
  let mut result := {}
  for id in shards do
    let some (modules, lines) ← readShard (shardPath olean id) | continue
    for line in lines do
      if let some target := target? modules line then
        if wanted.contains target.name then
          if let some query := decode modules line then
            result := result.insert query.target.name query
  return result

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
      (← unsafe SearchCache.isBuilt #[overlay.baseRoot])
  return (← unsafe isFullBuilt roots) &&
    (← unsafe SearchCache.isBuilt roots)

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
  if queryReady && searchReady then return 0
  let index ← unsafe Cache.loadIndex roots (!queryReady)
  let queryCount ← if queryReady then pure 0 else unsafe buildFull roots index
  let searchCount ←
    if searchReady then pure 0 else unsafe SearchCache.build roots index
  return max queryCount searchCount

private unsafe def buildOverlay (roots : Array Name) (baseRoot : Name) :
    IO QueryOverlay.Data := do
  let base ← unsafe Cache.loadIndex #[baseRoot] true
  let graph ← unsafe QueryOverlay.buildGraph roots baseRoot base.modules
  let affected := graph.affectedNames
  let cached ← unsafe loadQueries #[baseRoot] affected
  let mut queries := {}
  for name in affected do
    let cached? := cached.find? name
    let target? := graph.local? name <|> cached?.map (·.target)
    if let some target := target? then
      queries := queries.insert name (graph.queryFromBase base target cached?)
  let overlay := { graph with queries }
  unsafe QueryOverlay.save roots overlay
  return overlay

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

private unsafe def resolveFull (roots : Array Name) (query : String) :
    IO (Except String (Option CachedQuery)) := do
  let name := query.toName
  let some (modules, lines) ← unsafe loadShard roots name | return .ok none
  let wanted := query.toLower
  let mut exact := #[]
  let mut suffix := #[]
  for line in lines do
    let some target := target? modules line | continue
    if target.name == name then
      if let some cached := decode modules line then return .ok (some cached)
    else if NameResolve.exactMatch name target.name then
      if let some cached := decode modules line then exact := exact.push cached
    else if name.isAtomic && NameResolve.leafMatches wanted target.name then
      suffix := suffix.push (target, line)
  if exact.size == 1 then return .ok (some exact[0]!)
  if exact.size > 1 then
    return .error (NameResolve.ambiguityMessage query (exact.map (·.target)))
  if suffix.size == 1 then return .ok (decode modules suffix[0]!.2)
  if suffix.isEmpty then return .ok none
  return .error (NameResolve.ambiguityMessage query (suffix.map (·.1)))

private def localResolveMatches (overlay : QueryOverlay.Data) (query : String)
    (limit : Nat) : Array LocatedName :=
  NameResolve.collect query.toLower overlay.localNames.size
    (fun id => overlay.localNames[id]!) some (·.name) limit

private def localSearchMatches (overlay : QueryOverlay.Data)
    (pattern : SearchPattern) (limit : Nat) : Array LocatedName :=
  pattern.collect overlay.localNames.size (fun id => overlay.localNames[id]!)
    some (·.name) limit

private def mergeSearchResults (localResults baseResults : Array LocatedName)
    (limit : Nat) : Array LocatedName := Id.run do
  let mut byName : NameMap LocatedName := {}
  for target in baseResults do byName := byName.insert target.name target
  for target in localResults do byName := byName.insert target.name target
  let mut results := #[]
  for (_, target) in byName do results := results.push target
  return (results.qsort fun left right => Name.lt left.name right.name).take limit

private unsafe def exactFull (roots : Array Name) (query : String)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let name := query.toName
  let some (modules, lines) ← unsafe loadShard roots name | return none
  let mut results := #[]
  for line in lines do
    let some target := target? modules line | continue
    if NameResolve.exactMatch name target.name then
      results := results.push target
      if results.size == limit then break
  return some results

/-- Finds up to `limit` complete, case-sensitive user-name matches. -/
unsafe def exactMatches (roots : Array Name) (query : String)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let overlay? ← unsafe loadOverlay roots
  let some overlay := overlay? | return ← unsafe exactFull roots query limit
  let name := query.toName
  let localResults := overlay.localNames.filter
    (NameResolve.exactMatch name ·.name) |>.take limit
  if localResults.size == limit then return some localResults
  let some base ← unsafe exactFull #[overlay.baseRoot] query limit | return none
  return some (mergeSearchResults localResults base limit)

private unsafe def resolveFromLookup (roots : Array Name) (query : String) :
    IO (Except String (Option CachedQuery)) := do
  let some results ← unsafe SearchCache.lookup roots query 11 | return .ok none
  let candidates := NameResolve.bestBucket <|
    NameResolve.buckets query.toLower results.size
      (fun id => results[id]!) some (·.name) 11
  if candidates.size == 1 then
    return ← unsafe resolveFull roots candidates[0]!.name.toString
  if candidates.isEmpty then return .error (NameResolve.noMatchMessage query)
  return .error (NameResolve.ambiguityMessage query candidates)

private unsafe def overlayQuery? (overlay : QueryOverlay.Data)
    (target : LocatedName) : IO (Option CachedQuery) := do
  if let some cached := overlay.cached? target.name then return some cached
  if (overlay.local? target.name).isSome then return none
  match ← unsafe resolveFull #[overlay.baseRoot] target.name.toString with
  | .ok cached => return cached
  | .error _ => return none

/-- `none` means that a required cache is unavailable; a complete cached miss is an error. -/
unsafe def resolve (roots : Array Name) (query : String) :
    IO (Except String (Option CachedQuery)) := do
  let overlay? ← unsafe loadOverlay roots
  let some overlay := overlay? | do
    let exact ← unsafe resolveFull roots query
    match exact with
    | .ok none => return ← unsafe resolveFromLookup roots query
    | result => return result
  let name := query.toName
  if let some target := overlay.local? name then
    return .ok (overlay.cached? target.name)
  if let .ok (some cached) ← unsafe resolveFull #[overlay.baseRoot] query then
    if cached.target.name == name then
      return .ok (some <| (overlay.cached? cached.target.name).getD cached)
  let localResults := localResolveMatches overlay query 11
  let some base ← unsafe SearchCache.lookup #[overlay.baseRoot] query 11 |
    return .ok none
  let candidates := NameResolve.bestBucket <|
    NameResolve.mergeBuckets query.toLower 11 localResults base
  if candidates.size == 1 then
    return .ok (← unsafe overlayQuery? overlay candidates[0]!)
  if candidates.isEmpty then return .error (NameResolve.noMatchMessage query)
  return .error (NameResolve.ambiguityMessage query candidates)

unsafe def search (roots : Array Name) (pattern : SearchPattern)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let overlay? ← unsafe loadOverlay roots
  let some overlay := overlay? | do
    return ← unsafe SearchCache.search roots pattern limit
  let some base ← unsafe SearchCache.search #[overlay.baseRoot] pattern limit |
    return none
  return some <| mergeSearchResults
    (localSearchMatches overlay pattern limit) base limit

end LeanReach.QueryCache
