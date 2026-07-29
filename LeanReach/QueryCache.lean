import LeanReach.QueryOverlay

namespace LeanReach.QueryCache

open Lean

private def version := 9
private def shardCount := 1024

private def leaf : Name → String
  | .str _ value => value
  | .num _ value => toString value
  | .anonymous => ""

private def shard (name : Name) : Nat :=
  (hash (leaf name).toLower % UInt64.ofNat shardCount).toNat

private def shardPath (olean : System.FilePath) (id : Nat) : System.FilePath :=
  olean.withExtension s!"leanreach-query-{version}-{id}"

private def markerPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension s!"leanreach-query-root-{version}"

private def ready (olean : System.FilePath) (depHash : String) : IO Bool := do
  let path := markerPath olean
  unless ← path.pathExists do return false
  try return (← IO.FS.readFile path) == depHash
  catch _ => return false

private def allLocated (query : CachedQuery) : Array LocatedName :=
  #[query.target] ++ query.upstream ++ query.downstream

private def encodeShard (queries : Array CachedQuery) : String := Id.run do
  let mut ids : NameMap Nat := {}
  let mut modules := #[]
  for query in queries do
    for item in allLocated query do
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

private def decodeLocated (modules : Array Name) (fields : List String) :
    Option (Array LocatedName) :=
  go fields #[]
where
  go : List String → Array LocatedName → Option (Array LocatedName)
    | [], items => some items
    | name :: moduleId :: rest, items => do
      let some moduleName := moduleId.toNat? >>= fun id => modules[id]? | none
      go rest (items.push { name := name.toName, moduleName })
    | _, _ => none

private def decode (modules : Array Name) (line : String) : Option CachedQuery := do
  let name :: moduleId :: fields := line.splitOn "\t" | none
  let some moduleName := moduleId.toNat? >>= fun id => modules[id]? | none
  let (upstream, downstream) := fields.span (· != "|")
  let _ :: downstream := downstream | none
  return {
    target := { name := name.toName, moduleName }
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

unsafe def isBuilt (roots : Array Name) : IO Bool := do
  if roots.size > 1 && (← unsafe QueryOverlay.isBuilt roots) then return true
  else unsafe isFullBuilt roots

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

private unsafe def baseRoot? (roots : Array Name) : IO (Option Name) := do
  if roots.size < 2 then return none
  if roots.contains `Mathlib then
    return if ← unsafe isFullBuilt #[`Mathlib] then some `Mathlib else none
  for root in roots do
    if ← unsafe isFullBuilt #[root] then return some root
  return none

unsafe def build (roots : Array Name) : IO Nat := do
  if ← unsafe isBuilt roots then return 0
  if let some baseRoot ← unsafe baseRoot? roots then
    let base ← unsafe Cache.loadIndex #[baseRoot] false
    let baseModules := base.modules.foldl (init := ({} : NameHashSet)) (·.insert ·)
    return ← unsafe QueryOverlay.build roots baseRoot baseModules
  unsafe buildFull roots (← unsafe Cache.loadIndex roots true)

private def findExact (modules : Array Name) (lines : List String)
    (name : Name) : Option CachedQuery := do
  let needle := name.toString ++ "\t"
  for line in lines do
    if line.startsWith needle then return (← decode modules line)
  none

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

private unsafe def loadFull (roots : Array Name) (name : Name) :
    IO (Option CachedQuery) := do
  let some (modules, lines) ← unsafe loadShard roots name | return none
  return findExact modules lines name

private unsafe def resolveFull (roots : Array Name) (query : String) :
    IO (Except String (Option CachedQuery)) := do
  let name := query.toName
  let some (modules, lines) ← unsafe loadShard roots name | return .ok none
  if let some cached := findExact modules lines name then return .ok (some cached)
  unless name.isAtomic do return .ok none
  let wanted := query.toLower
  let candidates := lines.filterMap fun line =>
    match line.splitOn "\t" with
    | candidate :: _ =>
      if (leaf candidate.toName).toLower == wanted then some (candidate, line) else none
    | _ => none
  if let [(_, line)] := candidates then return .ok (decode modules line)
  if candidates.isEmpty then return .ok none
  let options := candidates.take 10 |>.map fun (name, _) => s!"  {name}"
  return .error s!"ambiguous declaration '{query}':\n{String.intercalate "\n" options}"

private def target? (modules : Array Name) (line : String) : Option LocatedName := do
  let name :: moduleId :: _ := line.splitOn "\t" | none
  let some moduleName := moduleId.toNat? >>= fun id => modules[id]? | none
  return { name := name.toName, moduleName }

private unsafe def searchFull (roots : Array Name) (query : String)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let name := query.toName
  let some (modules, lines) ← unsafe loadShard roots name | return none
  let wanted := query.toLower
  let mut exact := #[]
  let mut suffix := #[]
  for line in lines do
    let some target := target? modules line | continue
    let lower := target.name.toString.toLower
    if lower == wanted then
      exact := exact.push target
    else if name.isAtomic && (leaf target.name).toLower == wanted then
      suffix := suffix.push target
  let results := (exact ++ suffix).take limit
  return if results.isEmpty then none else some results

private def localMatches (overlay : QueryOverlay.Data) (query : String) :
    Array LocatedName :=
  let name := query.toName
  let wanted := query.toLower
  overlay.localNames.filter fun target =>
    let lower := target.name.toString.toLower
    lower == wanted || name.isAtomic && (leaf target.name).toLower == wanted

private def mergeMatches (query : String) (limit : Nat)
    (left right : Array LocatedName) : Array LocatedName := Id.run do
  let wanted := query.toLower
  let mut seen : NameHashSet := {}
  let mut exact := #[]
  let mut suffix := #[]
  for target in left ++ right do
    unless seen.contains target.name do
      seen := seen.insert target.name
      if target.name.toString.toLower == wanted then exact := exact.push target
      else suffix := suffix.push target
  exact := exact.qsort fun a b => Name.lt a.name b.name
  suffix := suffix.qsort fun a b => Name.lt a.name b.name
  return (exact ++ suffix).take limit

unsafe def load (roots : Array Name) (name : Name) : IO (Option CachedQuery) := do
  let overlay? ← if roots.size > 1 then unsafe QueryOverlay.load roots else pure none
  let some overlay := overlay? |
    return ← unsafe loadFull roots name
  let base ← unsafe Cache.loadIndex #[overlay.baseRoot] true
  let some target := overlay.local? name <|> base.located? name | return none
  return some (overlay.query base target)

unsafe def resolve (roots : Array Name) (query : String) :
    IO (Except String (Option CachedQuery)) := do
  let overlay? ← if roots.size > 1 then unsafe QueryOverlay.load roots else pure none
  let some overlay := overlay? |
    return ← unsafe resolveFull roots query
  let base ← unsafe Cache.loadIndex #[overlay.baseRoot] true
  let name := query.toName
  if let some target := overlay.local? name <|> base.located? name then
    return .ok (some (overlay.query base target))
  unless name.isAtomic do return .ok none
  let localResults := localMatches overlay query
  let baseMatches := (base.search query 11).filterMap base.located?
    |>.filter fun target => (leaf target.name).toLower == query.toLower
  let candidates := mergeMatches query 11 localResults baseMatches
  if candidates.size == 1 then return .ok (some (overlay.query base candidates[0]!))
  if candidates.isEmpty then return .ok none
  let options := candidates.take 10 |>.map fun target => s!"  {target.name}"
  return .error s!"ambiguous declaration '{query}':\n{String.intercalate "\n" options.toList}"

unsafe def search (roots : Array Name) (query : String)
    (limit : Nat) : IO (Option (Array LocatedName)) := do
  let overlay? ← if roots.size > 1 then unsafe QueryOverlay.load roots else pure none
  let some overlay := overlay? |
    return ← unsafe searchFull roots query limit
  let base := (← unsafe searchFull #[overlay.baseRoot] query limit).getD #[]
  let results := mergeMatches query limit (localMatches overlay query) base
  return if results.isEmpty then none else some results

end LeanReach.QueryCache
