import LeanReach.Cache

namespace LeanReach.QueryCache

open Lean

private def version := 4
private def shardCount := 1024

private def shard (name : Name) : Nat :=
  (name.hash % UInt64.ofNat shardCount).toNat

private def shardPath (olean : System.FilePath) (id : Nat) : System.FilePath :=
  olean.withExtension s!"leanreach-query-{version}-{id}"

private def markerPath (olean : System.FilePath) : System.FilePath :=
  olean.withExtension s!"leanreach-query-root-{version}"

private def ready (olean : System.FilePath) (depHash : String) : IO Bool := do
  let path := markerPath olean
  unless ← path.pathExists do return false
  try return (← IO.FS.readFile path) == depHash
  catch _ => return false

private def locatedFields (items : Array LocatedName) : List String :=
  items.toList.flatMap fun item => [item.name.toString, item.moduleName.toString]

private def encode (query : CachedQuery) : String :=
  String.intercalate "\t" <|
    [query.target.name.toString, query.target.moduleName.toString] ++
    locatedFields query.upstream ++ ["|"] ++ locatedFields query.downstream

private def decodeLocated (fields : List String) : Option (Array LocatedName) :=
  go fields #[]
where
  go : List String → Array LocatedName → Option (Array LocatedName)
    | [], items => some items
    | name :: moduleName :: rest, items =>
      go rest (items.push { name := name.toName, moduleName := moduleName.toName })
    | _, _ => none

private def decode (line : String) : Option CachedQuery := do
  let name :: moduleName :: fields := line.splitOn "\t" | none
  let (upstream, downstream) := fields.span (· != "|")
  let _ :: downstream := downstream | none
  return {
    target := { name := name.toName, moduleName := moduleName.toName }
    upstream := ← decodeLocated upstream
    downstream := ← decodeLocated downstream
  }

private def buildShards (index : Index) (start stop : Nat) :
    Array (Array String) := Id.run do
  let mut shards : Array (Array String) := Array.replicate shardCount #[]
  for id in [start:stop] do
    let query := index.cachedQueryAt! id
    shards := shards.modify (shard query.target.name) (·.push (encode query))
  return shards

unsafe def isBuilt (roots : Array Name) : IO Bool := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  ready olean depHash

unsafe def build (roots : Array Name) (index : Index) : IO Nat := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  if ← ready olean depHash then return 0
  let mut shards : Array (Array String) := Array.replicate shardCount #[]
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
      IO.asTask <| IO.FS.writeFile (shardPath olean id)
        (String.intercalate "\n" shards[id]!.toList)
    tasks.forM fun task => IO.ofExcept task.get
    offset := stop
  IO.FS.writeFile (markerPath olean) depHash
  return index.size

unsafe def load (roots : Array Name) (name : Name) : IO (Option CachedQuery) := do
  let (olean, depHash, _) ← unsafe Cache.rootData roots
  unless ← ready olean depHash do return none
  let path := shardPath olean (shard name)
  unless ← path.pathExists do return none
  let needle := name.toString ++ "\t"
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.startsWith needle then return decode line
  return none

end LeanReach.QueryCache
