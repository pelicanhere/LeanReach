import LeanReach.Cache

namespace LeanReach.QueryCache

open Lean

private def version := 6
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

unsafe def isBuilt (roots : Array Name) : IO Bool := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  ready olean depHash

unsafe def build (roots : Array Name) (index : Index) : IO Nat := do
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

unsafe def load (roots : Array Name) (name : Name) : IO (Option CachedQuery) := do
  let some (modules, lines) ← unsafe loadShard roots name | return none
  return findExact modules lines name

unsafe def resolve (roots : Array Name) (query : String) :
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

end LeanReach.QueryCache
