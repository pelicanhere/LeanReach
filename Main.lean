import LeanReach
import Lake.CLI.Error
import Lake.Util.Cli

namespace LeanReach.Cli

open Lean

inductive Command where
  | query (name : String)
  | search (pattern : String)
  | cache (modules : Array Name)

structure Config where
  root? : Option Name := none
  limit? : Option Nat := none
  interactive : Bool := false
  json : Bool := false
  profile : Bool := false
  help : Bool := false

abbrev CliMainM := ExceptT Lake.CliError IO
abbrev CliStateM := StateT Config CliMainM
abbrev CliM := Lake.ArgsT CliStateM

private def takeArg (option : String) : CliM String := do
  let some value ← Lake.takeArg? | throw <| Lake.CliError.missingArg option
  return value

private def takeNat (option : String) : CliM Nat := do
  let value ← takeArg option
  let some number := value.toNat? |
    throw <| Lake.CliError.invalidOptArg option "a natural number"
  return number

private def shortOption : Char → CliM PUnit
  | 'm' => do modifyThe Config ({ · with root? := some (← takeArg "-m").toName })
  | 'n' => do modifyThe Config ({ · with limit? := some (← takeNat "-n") })
  | 'i' => modifyThe Config ({ · with interactive := true })
  | 'j' => modifyThe Config ({ · with json := true })
  | 'h' => modifyThe Config ({ · with help := true })
  | option => throw <| Lake.CliError.unknownShortOption option

private def longOption : String → CliM PUnit
  | "--module" => shortOption 'm'
  | "--limit" => shortOption 'n'
  | "--interactive" => shortOption 'i'
  | "--json" => shortOption 'j'
  | "--help" => shortOption 'h'
  | "--profile" => modifyThe Config ({ · with profile := true })
  | option => throw <| Lake.CliError.unknownLongOption option

private def option :=
  Lake.option {
    short := shortOption
    long := longOption
    longShort := Lake.shortOptionWithArg shortOption
  }

private def usage := "\
LeanReach — Lean declaration search and dependency navigation

USAGE:
  leanreach [OPTIONS] DECLARATION
  leanreach [OPTIONS] search PATTERN
  leanreach [OPTIONS] cache [MODULE...]
  leanreach [OPTIONS] --interactive

OPTIONS:
  -m, --module MODULE   override the detected local library or Mathlib root
  -n, --limit N         override both dependency limits (default: 10 each)
  -i, --interactive     reuse one environment; read queries from stdin
  -j, --json            emit JSON (NDJSON in interactive mode)
      --profile         print elapsed and cache-stage time to stderr
  -h, --help            show this help

Without `--module`, combine built local lean_lib roots with required Mathlib.
With no modules, `cache` precomputes pretty-printed declarations for the detected view.
In interactive mode, enter a declaration name or `search PATTERN` on each line.
"

private def location (declaration : Declaration) : String :=
  s!"{declaration.file.getD declaration.moduleName}:{declaration.line}:{declaration.column}"

private def printDeclaration (indent : String) (declaration : Declaration) : IO Unit := do
  let continuation := String.ofList (List.replicate indent.length ' ')
  IO.println <| indent ++ declaration.signature.replace "\n" ("\n" ++ continuation)
  IO.println s!"{indent}  {location declaration}"

private def printRelated (label : String) (items : Array Declaration) : IO Unit := do
  IO.println s!"{label} ({items.size})"
  if items.isEmpty then IO.println "  <none>"
  for (declaration, index) in items.zipIdx do
    printDeclaration s!"  [{index + 1}] " declaration

private def printQuery (json : Bool) (result : QueryResult) : IO Unit := do
  if json then
    IO.println (toJson result).compress
  else
    printDeclaration "target  " result.target
    printRelated "upstream" result.upstream
    printRelated "downstream" result.downstream

private def printSearch (json : Bool) (query : String) (items : Array Declaration) : IO Unit := do
  if json then
    IO.println (Json.mkObj [("query", toJson query), ("items", toJson items)]).compress
  else
    IO.println s!"matches ({items.size})"
    for declaration in items do
      printDeclaration "  " declaration

private def Config.limits (config : Config) : Limits :=
  config.limit?.map Limits.uniform |>.getD {}

private def printPP (config : Config) (modules : Array Name)
    (result : Nat × PPTiming) : IO Unit := do
  let (count, timing) := result
  if config.json then
    IO.println <| (Json.mkObj [
      ("modules", toJson <| modules.map (·.toString)),
      ("declarations", toJson count)
    ]).compress
  else
    IO.println s!"pretty-printed {count} declarations"
  if config.profile then IO.eprintln s!"leanreach: pp {timing.profile}"

private inductive Prepared where
  | query (names : QueryNames)
  | search (pattern : String) (names : Array Name)

private def prepare (config : Config) (command : Command) (index : Index) :
    Except String (SessionPlan Prepared) :=
  match command with
    | .query query => do
      let names ← index.queryNames query config.limits
      return (.query names, names.all, some names.target)
    | .search pattern =>
      let names := index.search pattern config.limits.search
      return (.search pattern names, names, none)
    | .cache _ => throw "cache is not an interactive query"

private def runPrepared (session : Session) (config : Config) : Prepared → CoreM Unit
  | .query names => do printQuery config.json (← session.describeQuery names)
  | .search pattern names => do
    printSearch config.json pattern (← session.describeNames names)

private def profiled {α : Type} (enabled : Bool) (label : String)
    (action : IO α) : IO α := do
  unless enabled do return ← action
  let started ← IO.monoNanosNow
  let report := do
    let elapsed := (← IO.monoNanosNow) - started
    let duration :=
      if elapsed < 1000000 then s!"{max 1 (elapsed / 1000)}μs"
      else s!"{elapsed / 1000000}ms"
    IO.eprintln s!"leanreach: {label}={duration}"
  try
    let result ← action
    report
    return result
  catch error =>
    report
    throw error

private def parseLine (line : String) : Command :=
  if let some pattern := line.dropPrefix? "search " then
    .search pattern.trimAscii.copy
  else
    .query line

private partial def runInteractive (session : Session) (runner : InteractiveRunner)
    (config : Config) : IO Unit := do
  let line := (← (← IO.getStdin).getLine).trimAscii.copy
  if line.isEmpty then return
  let command := parseLine line
  let label := if command matches .search _ then "search" else "query"
  profiled config.profile label do
    try
      match command with
      | .query query =>
        runner.query query config.limits fun names =>
          runPrepared session config (.query names)
      | .search pattern =>
        runner.search pattern config.limits.search fun names =>
          runPrepared session config (.search pattern names)
      | .cache _ => unreachable!
    catch error =>
      let message := toString error
      if config.json then
        IO.println (Json.mkObj [("error", toJson message)]).compress
      else
        IO.eprintln s!"leanreach: {message}"
  (← IO.getStdout).flush
  runInteractive session runner config

private def validate (config : Config) : CliMainM Unit := do
  if let some limit := config.limit? then
    if limit == 0 || limit > 1000 then
      throw <| Lake.CliError.invalidOptArg "--limit" "an integer from 1 to 1000"

private unsafe def Config.roots (config : Config) (refresh := false) : IO (Array Name) :=
  config.root?.map (#[·]) |>.getDM (detectRoots refresh)

private unsafe def execute (config : Config) (command? : Option Command) : IO UInt32 := do
  match command? with
  | some (.cache modules) =>
    profiled config.profile "cache" do
      if modules.isEmpty then
        let result ← buildPPRoots (← config.roots true) fun moduleName done total =>
          unless config.json do
            if done == total || done % 100 == 0 then
              IO.eprintln s!"leanreach: pretty-printed modules {done}/{total} ({moduleName})"
        printPP config modules result
      else
        printPP config modules (← buildPPModules modules)
  | some (.query query) =>
    profiled config.profile "query" do
      let roots ← config.roots
      let limits := config.limits
      if (← withCachedQueryFor roots query limits fun session names =>
          runPrepared session config (.query names)).isNone then
        withSessionFor roots (prepare config (.query query)) true
          (runPrepared · config)
  | some (.search pattern) =>
    profiled config.profile "search" do
      let roots ← config.roots
      if (← withCachedSearchFor roots pattern config.limits.search fun session names =>
          runPrepared session config (.search pattern names)).isNone then
        withSessionFor roots (prepare config (.search pattern)) false
          (runPrepared · config)
  | none =>
    withInteractiveSession (← config.roots) fun session runner =>
      runInteractive session runner config
  return 0

private unsafe def cli : CliM UInt32 := do
  Lake.processOptions option
  let config ← getThe Config
  validate config
  let arguments ← Lake.takeArgs
  if config.help || arguments.isEmpty && !config.interactive then
    IO.println usage
    return 0
  let command ←
    if config.interactive then
      if arguments.isEmpty then pure none
      else throw <| Lake.CliError.unexpectedArguments arguments
    else
      match arguments with
      | ["search", pattern] => pure (some (.search pattern))
      | "cache" :: modules => pure (some (.cache <| modules.toArray.map (·.toName)))
      | [name] => pure (some (.query name))
      | arguments => throw <| Lake.CliError.unexpectedArguments arguments
  unsafe execute config command

unsafe def main (args : List String) : IO UInt32 := do
  try
    match ← (cli.run' args |>.run' {}).run with
    | .ok code => return code
    | .error error =>
      IO.eprintln error.toString
      return 2
  catch error =>
    IO.eprintln s!"leanreach: {error}"
    return 1

end LeanReach.Cli

unsafe def main (args : List String) : IO UInt32 :=
  LeanReach.Cli.main args
