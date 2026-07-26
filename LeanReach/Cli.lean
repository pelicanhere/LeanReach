import LeanReach.Interactive

namespace LeanReach.Cli

open Lean Lean.Core

inductive Command where
  | query (declaration : String)
  | search (pattern : String)
  deriving Repr

structure Config where
  command : Option Command := none
  imports : Array Name := #[]
  mode : DependencyMode := .source
  direction : Direction := .both
  depth : Nat := 1
  limit : Nat := 20
  includeInternal : Bool := false
  interactive : Bool := false
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

private def setCommand (config : Config) (command : Command) : Except String Config :=
  match config.command with
  | none => .ok { config with command := some command }
  | some _ => .error "only one query or search pattern may be provided"

private partial def parseArgs (args : List String) (config : Config := {}) :
    Except String Config := do
  match args with
  | [] => return config
  | "-h" :: rest =>
    parseArgs rest { config with help := true }
  | "--help" :: rest =>
    parseArgs rest { config with help := true }
  | "--version" :: rest =>
    parseArgs rest { config with version := true }
  | "-j" :: rest =>
    parseArgs rest { config with json := true }
  | "--json" :: rest =>
    parseArgs rest { config with json := true }
  | "--profile" :: rest =>
    parseArgs rest { config with profile := true }
  | "--interactive" :: rest =>
    parseArgs rest { config with interactive := true }
  | "--include-internal" :: rest =>
    parseArgs rest { config with includeInternal := true }
  | "--upstream" :: rest =>
    parseArgs rest { config with direction := .upstream }
  | "--downstream" :: rest =>
    parseArgs rest { config with direction := .downstream }
  | "--mode" :: mode :: rest =>
    let mode ← LeanReach.parseDependencyMode "--mode" mode
    parseArgs rest { config with mode }
  | "--mode" :: [] =>
    throw "missing value after --mode"
  | "--direction" :: direction :: rest =>
    let direction ← LeanReach.parseDirection "--direction" direction
    parseArgs rest { config with direction }
  | "--direction" :: [] =>
    throw "missing value after --direction"
  | "-d" :: value :: rest =>
    let depth ← LeanReach.parseDepth "--depth" value
    parseArgs rest { config with depth }
  | "--depth" :: value :: rest =>
    let depth ← LeanReach.parseDepth "--depth" value
    parseArgs rest { config with depth }
  | "-d" :: [] =>
    throw "missing value after --depth"
  | "--depth" :: [] =>
    throw "missing value after --depth"
  | "-n" :: value :: rest =>
    let limit ← LeanReach.parseLimit "--limit" value
    parseArgs rest { config with limit }
  | "--limit" :: value :: rest =>
    let limit ← LeanReach.parseLimit "--limit" value
    parseArgs rest { config with limit }
  | "-n" :: [] =>
    throw "missing value after --limit"
  | "--limit" :: [] =>
    throw "missing value after --limit"
  | "-m" :: value :: rest =>
    parseArgs rest { config with imports := config.imports.push value.toName }
  | "--module" :: value :: rest =>
    parseArgs rest { config with imports := config.imports.push value.toName }
  | "--import" :: value :: rest =>
    parseArgs rest { config with imports := config.imports.push value.toName }
  | "-m" :: [] =>
    throw "missing module name"
  | "--module" :: [] =>
    throw "missing module name"
  | "--import" :: [] =>
    throw "missing module name"
  | "query" :: declaration :: rest =>
    parseArgs rest (← setCommand config (.query declaration))
  | "query" :: [] =>
    throw "missing declaration after query"
  | "search" :: pattern :: rest =>
    parseArgs rest (← setCommand config (.search pattern))
  | "search" :: [] =>
    throw "missing pattern after search"
  | argument :: rest =>
    if argument.startsWith "-" then
      throw s!"unknown option '{argument}'"
    parseArgs rest (← setCommand config (.query argument))

private def importsOrDefault (config : Config) : Array Name :=
  if config.imports.isEmpty then #["Mathlib".toName] else config.imports

private def runCommand (config : Config) : CoreM UInt32 := do
  if config.interactive then
    LeanReach.runInteractive {
      mode := config.mode
      direction := config.direction
      depth := config.depth
      limit := config.limit
      includeInternal := config.includeInternal
      profile := config.profile
    }
  else match config.command with
  | some (.query declaration) =>
    let result ← LeanReach.runQuery {
      query := declaration
      mode := config.mode
      direction := config.direction
      depth := config.depth
      limit := config.limit
      includeInternal := config.includeInternal
    }
    match result with
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
    let result ← LeanReach.runSearch pattern config.limit config.includeInternal
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
  enableInitializersExecution
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
      let activity := if config.interactive then "session" else "query"
      IO.eprintln s!"leanreach profile: init={initialized - started}ms \
        import={loaded - initialized}ms {activity}={finished - loaded}ms \
        total={finished - started}ms"
    return exitCode
  finally
    env.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error message =>
    IO.eprintln s!"leanreach: {message}"
    IO.eprintln "Try 'leanreach --help'."
    return 2
  | .ok config =>
    if config.help then
      IO.println usage
      return 0
    if config.version then
      IO.println "leanreach 0.1.0"
      return 0
    if !config.interactive && config.command.isNone then
      IO.eprintln "leanreach: no declaration or search pattern provided"
      IO.eprintln "Try 'leanreach --help'."
      return 2
    if config.interactive && config.command.isSome then
      IO.eprintln "leanreach: --interactive does not accept a positional query or search command"
      IO.eprintln "Send requests on stdin instead."
      return 2
    try
      execute config
    catch error =>
      IO.eprintln s!"leanreach: {error}"
      return 1

end LeanReach.Cli

unsafe def main (args : List String) : IO UInt32 :=
  LeanReach.Cli.main args
