import LeanReach.Cache.Index
import LeanReach.Cache.Overlay
import LeanReach.Cache.Search
import LeanReach.Search.Match

namespace LeanReach.QueryCache

open Lean

private def version := 10
private def shardCount := 1024

private def shard (name : Name) : Nat :=
  (hash (NameSearch.leaf name).toLower % UInt64.ofNat shardCount).toNat

private def shardPath (olean : System.FilePath) (id : Nat) : System.FilePath :=
  olean.withExtension s!"leanreach-query-{version}-{id}"

private def markerPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension s!"leanreach-query-root-{version}"

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

private unsafe def loadOverlay (roots : Array Name) : IO (Option QueryOverlay.Data) := do
  if let some overlay ← unsafe readOverlay roots then return some overlay
  let some baseRoot ← unsafe baseRoot? roots | return none
  return some (← unsafe QueryOverlay.build roots baseRoot)

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

unsafe def build (roots : Array Name) : IO Nat := do
  if let some overlay ← unsafe readOverlay roots then
    return ← unsafe buildFullCaches #[overlay.baseRoot]
  if let some baseRoot ← unsafe baseRoot? roots then
    let overlay ← unsafe QueryOverlay.build roots baseRoot
    return max overlay.size (← unsafe buildFullCaches #[baseRoot])
  unsafe buildFullCaches roots

private def target? (modules : Array Name) (line : String) : Option LocatedName := do
  let name :: moduleId :: _ := line.splitOn "\t" | none
  decodeTarget modules name moduleId

private def exactMatches (modules : Array Name) (lines : List String)
    (name : Name) : Array CachedQuery := Id.run do
  let mut results := #[]
  for line in lines do
    if let some query := decode modules line then
      if query.target.name == name ||
          (!isPrivateName name && privateToUserName query.target.name == name) then
        results := results.push query
  return results

private unsafe def loadShard (roots : Array Name) (name : Name) :
    IO (Option (Array Name × List String)) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unless ← ready olean depHash do return none
  let path := shardPath olean (shard name)
  unless ← path.pathExists do return none
  let content ← IO.FS.readFile path
  let (modules, queries) := content.splitOn "\n" |>.span (· != "|")
  let _ :: queries := queries | return none
  return some (modules.toArray.map (·.toName), queries)

private unsafe def resolveFull (roots : Array Name) (query : String) :
    IO (Except String (Option CachedQuery)) := do
  let name := query.toName
  let some (modules, lines) ← unsafe loadShard roots name | return .ok none
  let exact := exactMatches modules lines name
  if exact.size == 1 then return .ok (some exact[0]!)
  if exact.size > 1 then
    let options := exact.take 10 |>.map fun cached =>
      s!"  {privateToUserName cached.target.name} ({cached.target.moduleName})"
    return .error s!"ambiguous declaration '{query}':\n{String.intercalate "\n" options.toList}"
  unless name.isAtomic do return .ok none
  let wanted := query.toLower
  let candidates := lines.filterMap fun line => do
    let some target := target? modules line | none
    if NameSearch.leafMatches wanted (privateToUserName target.name) then
      some (target, line)
    else none
  if let [(_, line)] := candidates then return .ok (decode modules line)
  if candidates.isEmpty then return .ok none
  let options := candidates.take 10 |>.map fun (target, _) =>
    s!"  {privateToUserName target.name} ({target.moduleName})"
  return .error s!"ambiguous declaration '{query}':\n{String.intercalate "\n" options}"

private unsafe def searchFull (roots : Array Name) (query : String)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let name := query.toName
  let some (modules, lines) ← unsafe loadShard roots name | return none
  let wanted := query.toLower
  let mut exact := #[]
  let mut suffix := #[]
  for line in lines do
    let some target := target? modules line | continue
    if NameSearch.exact wanted target.name then
      exact := exact.push target
    else if name.isAtomic && NameSearch.leafMatches wanted target.name then
      suffix := suffix.push target
  let results := (exact ++ suffix).take limit
  return if results.isEmpty then none else some results

private def localMatches (overlay : QueryOverlay.Data) (query : String) :
    Array LocatedName :=
  let name := query.toName
  let wanted := query.toLower
  overlay.localNames.filter fun target =>
    NameSearch.exact wanted target.name ||
      name.isAtomic && NameSearch.leafMatches wanted target.name

private def mergeMatches (query : String) (limit : Nat)
    (left right : Array LocatedName) : Array LocatedName := Id.run do
  let mut seen : NameHashSet := {}
  let mut candidates := #[]
  for target in left ++ right do
    unless seen.contains target.name do
      seen := seen.insert target.name
      candidates := candidates.push target
  candidates := candidates.qsort fun a b => Name.lt a.name b.name
  return NameSearch.collect query candidates some (·.name) limit

unsafe def resolve (roots : Array Name) (query : String) :
    IO (Except String (Option CachedQuery)) := do
  let overlay? ← unsafe loadOverlay roots
  let some overlay := overlay? |
    return ← unsafe resolveFull roots query
  let base ← unsafe Cache.loadIndex #[overlay.baseRoot] true
  let name := query.toName
  if let some target := overlay.local? name <|> base.located? name then
    return .ok (some (overlay.query base target))
  let localResults := localMatches overlay query
  let baseMatches := (base.search query 11).filterMap base.located?
  let candidates := mergeMatches query 11 localResults baseMatches
  if candidates.size == 1 then return .ok (some (overlay.query base candidates[0]!))
  if candidates.isEmpty then return .ok none
  let options := candidates.take 10 |>.map fun target =>
    s!"  {privateToUserName target.name} ({target.moduleName})"
  return .error s!"ambiguous declaration '{query}':\n{String.intercalate "\n" options.toList}"

unsafe def search (roots : Array Name) (query : String)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let overlay? ← unsafe loadOverlay roots
  let some overlay := overlay? | do
    if let some results ← unsafe SearchCache.search roots query limit then
      return some results
    return ← unsafe searchFull roots query limit
  let some base ← unsafe SearchCache.search #[overlay.baseRoot] query limit |
    let base := (← unsafe searchFull #[overlay.baseRoot] query limit).getD #[]
    let results := mergeMatches query limit (localMatches overlay query) base
    return if results.isEmpty then none else some results
  let results := mergeMatches query limit overlay.localNames base
  return some results

end LeanReach.QueryCache
