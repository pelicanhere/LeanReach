import LeanReach.Interactive

namespace LeanReach.Cli

open Lean Lean.Core

inductive Command where
  | query (declaration : String)
  | search (pattern : String)
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
  lake exe leanreach Nat.gcd --module Mathlib.Data.Nat.GCD.Basic
  lake exe leanreach --interactive --module Mathlib.Data.Nat.GCD.Basic
"

private def importsOrDefault (config : Config) : Array Name :=
  if config.imports.isEmpty then #["Mathlib".toName] else config.imports

private def runCommand (config : Config) : CoreM UInt32 := do
  match config.command with
  | some .interactive =>
    LeanReach.runInteractive config.toQueryOptions config.profile
  | some (.query declaration) =>
    match ← LeanReach.runQuery declaration config.toQueryOptions with
    | .ok result =>
      if config.json then
        LeanReach.printJson result
      else
        LeanReach.printQueryHuman result
      return 0
    | .error failure =>
      if config.json then
        LeanReach.printJson failure
      else
        LeanReach.printFailureHuman failure
      return 2
  | some (.search pattern) =>
    let result ← LeanReach.runSearch pattern config.toQueryOptions
    if config.json then
      LeanReach.printJson result
    else
      LeanReach.printSearchHuman result
    return if result.items.isEmpty then 2 else 0
  | none =>
    IO.eprintln "leanreach: no declaration or search pattern provided"
    IO.eprintln "Try 'leanreach --help'."
    return 2

unsafe def execute (config : Config) : IO UInt32 := do
  let started ← IO.monoMsNow
  initSearchPath (← findSysroot)
  let initialized ← IO.monoMsNow
  let level := if config.mode == .kernel then OLeanLevel.private else OLeanLevel.server
  let env ← importModules ((importsOrDefault config).map ({ module := · })) {}
    (trustLevel := 1024) (loadExts := false) (level := level)
  try
    let loaded ← IO.monoMsNow
    let exitCode ← CoreM.toIO' (runCommand config)
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
