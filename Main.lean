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
  let some number := (← takeArg option).toNat? |
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
  -n, --limit N         override result limits (default: 10 each)
  -i, --interactive     reuse one environment; read queries from stdin
  -j, --json            emit JSON (NDJSON in interactive mode)
      --profile         print elapsed and cache-stage time to stderr
  -h, --help            show this help

Without `--module`, combine built local lean_lib roots with required Mathlib.
With no modules, `cache` precomputes pretty-printed declarations for the detected view.
In interactive mode, enter a declaration or `search PATTERN`.
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

private def printQueryNames (config : Config) (session : Session)
    (names : QueryNames) : IO Unit := do
  printQuery config.json (← session.describeQuery names)

private def printSearchNames (config : Config) (pattern : String)
    (session : Session) (names : Array Name) : IO Unit := do
  printSearch config.json pattern (← session.describeNames names)

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
    action
  finally
    report

private def parseLine (line : String) : Command :=
  if let some pattern := line.dropPrefix? "search " then
    .search pattern.copy
  else
    .query line.trimAscii.copy

private def chompLine (line : String) : String :=
  let line := (line.dropSuffix? "\n").map (·.copy) |>.getD line
  (line.dropSuffix? "\r").map (·.copy) |>.getD line

private def runInteractive (session : Session) (runner : InteractiveRunner)
    (config : Config) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  while true do
    let line := chompLine (← stdin.getLine)
    if line.trimAscii.isEmpty then break
    let command := parseLine line
    let label := match command with
      | .search _ => "search"
      | _ => "query"
    profiled config.profile label do
      try
        match command with
        | .query query =>
          runner.query query config.limits fun names =>
            printQueryNames config session names
        | .search source =>
          let pattern ← IO.ofExcept <|
            SearchPattern.compileRegex source |>.mapError IO.userError
          runner.search pattern config.limits.search fun names =>
            printSearchNames config source session names
        | .cache _ => unreachable!
      catch error =>
        let message := toString error
        if config.json then
          IO.println (Json.mkObj [("error", toJson message)]).compress
        else
          IO.eprintln s!"leanreach: {message}"
    stdout.flush

private def validate (config : Config) : CliMainM Unit := do
  if config.limit?.any fun limit => limit == 0 || limit > 1000 then
    throw <| Lake.CliError.invalidOptArg "--limit" "an integer from 1 to 1000"

private unsafe def Config.roots (config : Config) (refresh := false) : IO (Array Name) :=
  config.root?.map (#[·]) |>.getDM (detectRoots refresh)

private unsafe def execute (config : Config) (command? : Option Command) : IO UInt32 := do
  match command? with
  | some (.cache modules) =>
    profiled config.profile "cache" do
      if modules.isEmpty then
        let roots ← config.roots true
        let result ← buildPPRoots roots fun moduleName done total =>
          unless config.json do
            if done == total || done % 100 == 0 then
              IO.eprintln s!"leanreach: pretty-printed modules {done}/{total} ({moduleName})"
        printPP config roots result
      else
        printPP config modules (← buildPPModules modules)
  | some (.query query) =>
    profiled config.profile "query" do
      let roots ← config.roots
      withQueryFor roots query config.limits (printQueryNames config)
  | some (.search source) =>
    profiled config.profile "search" do
      let pattern ← IO.ofExcept <|
        SearchPattern.compileRegex source |>.mapError IO.userError
      let roots ← config.roots
      withSearchFor roots pattern config.limits.search
        (printSearchNames config source)
  | none =>
    withInteractiveSession (← config.roots) fun session runner =>
      runInteractive session runner config
  return 0

private partial def collectArguments (arguments : Array String := #[]) :
    CliM (Array String) := do
  let some argument ← Lake.takeArg? | return arguments
  if argument == "--" then
    return arguments ++ (← Lake.takeArgs).toArray
  if argument.length > 1 && argument.startsWith "-" then
    option argument
    collectArguments arguments
  else
    collectArguments (arguments.push argument)

private unsafe def cli : CliM UInt32 := do
  let arguments ← collectArguments
  let config ← getThe Config
  validate config
  if config.help || arguments.isEmpty && !config.interactive then
    IO.println usage
    return 0
  let command ←
    if config.interactive then
      if arguments.isEmpty then pure none
      else throw <| Lake.CliError.unexpectedArguments arguments.toList
    else
      match arguments.toList with
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
