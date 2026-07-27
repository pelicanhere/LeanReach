import LeanReach.Interactive

namespace LeanReach.Cli

open Lean

inductive Command where
  | query (declaration : String)
  | search (pattern : String)
  | index
  | interactive

structure Config extends QueryOptions where
  command : Option Command := none
  imports : Array Name := #[]
  json : Bool := false
  profile : Bool := false
  help : Bool := false
  version : Bool := false

private def usage : String := "\
LeanReach — semantic declaration neighborhoods for Lean

USAGE:
  leanreach [query] DECL [OPTIONS]
  leanreach search PATTERN [OPTIONS]
  leanreach index [OPTIONS]
  leanreach --interactive [OPTIONS]

OPTIONS:
  -m, --module MODULE       root MODULE; repeatable (default: Mathlib)
      --direction DIR       both, upstream, or downstream (default: both)
      --upstream            shorthand for --direction upstream
      --downstream          shorthand for --direction downstream
  -d, --depth N             dependency depth, 0..8 (default: 1)
  -n, --limit N             results per direction, 1..1000 (default: 20)
  -j, --json                emit structured JSON
      --interactive         serve newline-delimited JSON on stdin/stdout
      --include-internal    include generated/internal declarations
      --profile             print load/query timings to stderr
  -h, --help                show this help
      --version             show the version

EXAMPLES:
  lake exe leanreach Nat.gcd
  lake exe leanreach map --direction upstream --depth 2
  lake exe leanreach search prime_def --json
  lake exe leanreach index --profile
  lake exe leanreach Nat.gcd --module Mathlib.Data.Nat.GCD.Basic
  lake exe leanreach --interactive --module Mathlib.Data.Nat.GCD.Basic
"

private def importsOrDefault (config : Config) : Array Name :=
  if config.imports.isEmpty then #["Mathlib".toName] else config.imports

private def printQuery (config : Config) :
    Except QueryFailure QueryResult → IO UInt32
  | .ok result => do
    if config.json then
      LeanReach.printJson result
    else
      LeanReach.printQueryHuman result
    return 0
  | .error failure => do
    if config.json then
      LeanReach.printJson failure
    else
      LeanReach.printFailureHuman failure
    return 2

private def printSearch (config : Config) (result : SearchResult) : IO UInt32 := do
  if config.json then
    LeanReach.printJson result
  else
    LeanReach.printSearchHuman result
  return if result.items.isEmpty then 2 else 0

private def printIndex (config : Config) (index : SourceIndex.Index) : IO Unit := do
  if config.json then
    LeanReach.printJson <| Json.mkObj [
      ("declarations", toJson index.declarationCount),
      ("relations", toJson index.relationCount)
    ]
  else
    IO.println s!"source index: {index.declarationCount} declarations, \
      {index.relationCount} direct relations"

private def runCommand (command : Command) (config : Config) (index : SourceIndex.Index)
    (sourcePath : SearchPath) : IO UInt32 := do
  match command with
  | .interactive =>
    LeanReach.Interactive.run index sourcePath config.toQueryOptions config.profile
  | .query declaration =>
    printQuery config
      (← SourceIndex.runQuery index sourcePath declaration config.toQueryOptions)
  | .search pattern =>
    printSearch config
      (← SourceIndex.runSearch index sourcePath pattern config.toQueryOptions)
  | .index =>
    printIndex config index
    return 0

private unsafe def execute (config : Config) (command : Command) : IO UInt32 := do
  let started ← IO.monoMsNow
  initSearchPath (← findSysroot)
  let initialized ← IO.monoMsNow
  let roots := importsOrDefault config
  let sourcePath ← Query.sourceSearchPath
  let log := if config.profile then
      fun message => IO.eprintln s!"leanreach: {message}"
    else
      fun _ => pure ()
  unsafe SourceIndex.withIndex roots (log := log) fun index => do
    let loaded ← IO.monoMsNow
    let exitCode ← runCommand command config index sourcePath
    let finished ← IO.monoMsNow
    if config.profile then
      let activity := match command with
        | .interactive => "session"
        | .index => "command"
        | _ => "query"
      IO.eprintln s!"leanreach profile: init={initialized - started}ms \
        index={loaded - initialized}ms {activity}={finished - loaded}ms \
        total={finished - started}ms"
    return exitCode

unsafe def run (config : Config) : IO UInt32 := do
  if config.help then
    IO.println usage
    return 0
  if config.version then
    IO.println "leanreach 0.1.0"
    return 0
  let some command := config.command | do
    IO.eprintln "leanreach: no declaration or search pattern provided"
    IO.eprintln "Try 'leanreach --help'."
    return 2
  try
    execute config command
  catch error =>
    IO.eprintln s!"leanreach: {error}"
    return 1

end LeanReach.Cli
