import LeanReach.Interactive

namespace LeanReach.Cli

open Lean Lean.Core

inductive Command where
  | query (declaration : String)
  | search (pattern : String)
  | index
  | interactive
  deriving Repr

structure Config extends QueryOptions where
  command : Option Command := none
  imports : Array Name := #[]
  json : Bool := false
  profile : Bool := false
  help : Bool := false
  version : Bool := false
  deriving Repr

def usage : String := "\
LeanReach — semantic declaration neighborhoods for Lean

USAGE:
  leanreach [query] DECL [OPTIONS]
  leanreach search PATTERN [OPTIONS]
  leanreach index [OPTIONS]
  leanreach --interactive [OPTIONS]

OPTIONS:
  -m, --module MODULE       import MODULE; repeatable (default: Mathlib)
      --mode MODE           source or kernel (default: source)
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
  lake exe leanreach Nat.gcd --mode kernel --upstream
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
    IO.println <| Json.mkObj [
      ("declarations", toJson index.declarationCount),
      ("relations", toJson index.relationCount)
    ] |>.pretty
  else
    IO.println s!"source index: {index.declarationCount} declarations, \
      {index.relationCount} direct relations"

private def runCommand {m : Type → Type} [Monad m] [MonadLiftT IO m]
    (config : Config)
    (runQuery : String → m (Except QueryFailure QueryResult))
    (runSearch : String → m SearchResult)
    (runInteractive : m UInt32)
    (index? : Option SourceIndex.Index := none) : m UInt32 := do
  match config.command with
  | some .interactive =>
    runInteractive
  | some (.query declaration) =>
    printQuery config (← runQuery declaration)
  | some (.search pattern) =>
    printSearch config (← runSearch pattern)
  | some .index =>
    match index? with
    | some index =>
      printIndex config index
      return 0
    | none =>
      IO.eprintln "leanreach: index is only available in source mode"
      return 2
  | none =>
    IO.eprintln "leanreach: no declaration or search pattern provided"
    IO.eprintln "Try 'leanreach --help'."
    return 2

private unsafe def runIndexedInteractiveIO (config : Config) (index : SourceIndex.Index)
    (sourcePath : SearchPath) : IO UInt32 := do
  let env ← mkEmptyEnvironment (trustLevel := 1024)
  try
    CoreM.toIO'
      (LeanReach.runIndexedInteractive index sourcePath config.toQueryOptions config.profile)
      { fileName := "<leanreach>", fileMap := default }
      { env }
  finally
    env.freeRegions

private unsafe def executeSource (config : Config) (started initialized : Nat) :
    IO UInt32 := do
  let roots := importsOrDefault config
  let sourcePath ← Query.sourceSearchPath
  let log := if config.profile then
      fun message => IO.eprintln s!"leanreach: {message}"
    else
      fun _ => pure ()
  unsafe SourceIndex.withIndex roots (log := log) fun index => do
    let loaded ← IO.monoMsNow
    let exitCode ← runCommand config
      (fun declaration =>
        SourceIndex.runQuery index sourcePath declaration config.toQueryOptions)
      (fun pattern =>
        SourceIndex.runSearch index sourcePath pattern config.toQueryOptions)
      (unsafe runIndexedInteractiveIO config index sourcePath)
      (some index)
    let finished ← IO.monoMsNow
    if config.profile then
      let activity := match config.command with
        | some .interactive => "session"
        | some .index => "command"
        | _ => "query"
      IO.eprintln s!"leanreach profile: init={initialized - started}ms \
        index={loaded - initialized}ms {activity}={finished - loaded}ms \
        total={finished - started}ms"
    return exitCode

private unsafe def executeKernel (config : Config) (started initialized : Nat) :
    IO UInt32 := do
  let env ← importModules ((importsOrDefault config).map ({ module := · })) {}
    (trustLevel := 1024) (loadExts := false) (level := .private)
  try
    let loaded ← IO.monoMsNow
    let exitCode ← CoreM.toIO' (runCommand config
        (fun declaration => LeanReach.runQuery declaration config.toQueryOptions)
        (fun pattern => LeanReach.runSearch pattern config.toQueryOptions)
        (LeanReach.runInteractive config.toQueryOptions config.profile))
      { fileName := "<leanreach>", fileMap := default }
      { env }
    let finished ← IO.monoMsNow
    if config.profile then
      let activity := match config.command with
        | some .interactive => "session"
        | _ => "query"
      IO.eprintln s!"leanreach profile: init={initialized - started}ms \
        import={loaded - initialized}ms {activity}={finished - loaded}ms \
        total={finished - started}ms"
    return exitCode
  finally
    env.freeRegions

unsafe def execute (config : Config) : IO UInt32 := do
  let started ← IO.monoMsNow
  initSearchPath (← findSysroot)
  let initialized ← IO.monoMsNow
  match config.mode with
  | .source => unsafe executeSource config started initialized
  | .kernel =>
    match config.command with
    | some .index =>
      IO.eprintln "leanreach: index is only available in source mode"
      return 2
    | _ =>
      unsafe executeKernel config started initialized

unsafe def run (config : Config) : IO UInt32 := do
  if config.help then
    IO.println usage
    return 0
  if config.version then
    IO.println "leanreach 0.1.0"
    return 0
  if config.command.isNone then
    IO.eprintln "leanreach: no declaration or search pattern provided"
    IO.eprintln "Try 'leanreach --help'."
    return 2
  try
    execute config
  catch error =>
    IO.eprintln s!"leanreach: {error}"
    return 1

end LeanReach.Cli
