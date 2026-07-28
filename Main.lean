import LeanReach
import Lake.CLI.Error
import Lake.Util.Cli

namespace LeanReach.Cli

open Lean

inductive Command where
  | query (name : String)
  | search (pattern : String)
  | context (name : String)
  | cache (modules : Array Name)

structure Config where
  root : Name := `Mathlib
  depth : Nat := 1
  limit : Nat := 20
  upstream : Bool := true
  downstream : Bool := true
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
  | 'm' => do modifyThe Config ({ · with root := (← takeArg "-m").toName })
  | 'd' => do modifyThe Config ({ · with depth := ← takeNat "-d" })
  | 'n' => do modifyThe Config ({ · with limit := ← takeNat "-n" })
  | 'i' => modifyThe Config ({ · with interactive := true })
  | 'j' => modifyThe Config ({ · with json := true })
  | 'h' => modifyThe Config ({ · with help := true })
  | option => throw <| Lake.CliError.unknownShortOption option

private def longOption : String → CliM PUnit
  | "--module" => shortOption 'm'
  | "--depth" => shortOption 'd'
  | "--limit" => shortOption 'n'
  | "--interactive" => shortOption 'i'
  | "--json" => shortOption 'j'
  | "--help" => shortOption 'h'
  | "--profile" => modifyThe Config ({ · with profile := true })
  | "--upstream" =>
    modifyThe Config ({ · with upstream := true, downstream := false })
  | "--downstream" =>
    modifyThe Config ({ · with upstream := false, downstream := true })
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
  leanreach [OPTIONS] context DECLARATION
  leanreach [OPTIONS] cache MODULE...
  leanreach [OPTIONS] --interactive

OPTIONS:
  -m, --module MODULE   import root module (default: Mathlib)
  -d, --depth N         traversal depth (default: 1)
  -n, --limit N         maximum results per list (default: 20)
      --upstream        only declarations used by the target
      --downstream      only declarations that use the target
  -i, --interactive     reuse one environment; read queries from stdin
  -j, --json            emit JSON (NDJSON in interactive mode)
      --profile         print elapsed time to stderr
  -h, --help            show this help

Run through `lake env` with `--module Your.Root` to search a local library.
In interactive mode, enter a declaration name or `search PATTERN` on each line.
"

private def location (declaration : Declaration) : String :=
  s!"{declaration.file.getD declaration.moduleName}:{declaration.line}:{declaration.column}"

private def printDeclaration (indent : String) (declaration : Declaration) : IO Unit := do
  let continuation := String.ofList (List.replicate indent.length ' ')
  IO.println <| indent ++ declaration.signature.replace "\n" ("\n" ++ continuation)
  IO.println s!"{indent}  {location declaration}"

private def printRelated (label : String) (items : Array Related) : IO Unit := do
  IO.println s!"{label} ({items.size})"
  if items.isEmpty then IO.println "  <none>"
  for (distance, declaration) in items do
    let marker := s!"  [{distance}] "
    IO.println <| marker ++ declaration.signature.replace "\n" "\n      "
    IO.println s!"      {location declaration}"

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

private def printContext (json : Bool) (target : Declaration)
    (items : Array RankedDeclaration) : IO Unit := do
  if json then
    IO.println (Json.mkObj [("target", toJson target), ("context", toJson items)]).compress
  else
    printDeclaration "target  " target
    IO.println s!"context ({items.size})"
    if items.isEmpty then IO.println "  <none>"
    for item in items do
      IO.println s!"  [score {item.score}, depth {item.distance}, df {item.documentFrequency}]"
      printDeclaration "    " item.declaration

private def runOne (session : Session) (config : Config) (command : Command) : CoreM Unit := do
  match command with
  | .query name =>
    printQuery config.json (← session.query name {
      depth := config.depth
      limit := config.limit
      upstream := config.upstream
      downstream := config.downstream
    })
  | .search pattern =>
    printSearch config.json pattern (← session.search pattern config.limit)
  | .context name =>
    let (target, items) ← session.context name config.depth config.limit
    printContext config.json target items
  | .cache modules =>
    let count ← session.cacheModules modules
    if config.json then
      IO.println <| (Json.mkObj [
        ("modules", toJson <| modules.map (·.toString)),
        ("declarations", toJson count)
      ]).compress
    else
      IO.println s!"cached {count} declarations"

private def runTimed (session : Session) (config : Config) (command : Command) : CoreM Unit := do
  let started ← IO.monoMsNow
  runOne session config command
  if config.profile then
    IO.eprintln s!"leanreach: query={(← IO.monoMsNow) - started}ms"

private def commandNames (config : Config) (command : Command) (index : Index) :
    Except String (Array Name) := do
  match command with
  | .query query =>
    let (target, upstream, downstream) ← index.queryNames query {
      depth := config.depth
      limit := config.limit
      upstream := config.upstream
      downstream := config.downstream
    }
    return #[target] ++ upstream.map (·.2) ++ downstream.map (·.2)
  | .search pattern =>
    return index.search pattern config.limit
  | .context query =>
    let (target, context) ← index.contextNames query config.depth config.limit
    return #[target] ++ context.map (·.2.2)
  | .cache modules =>
    return index.namesInModules modules

private def parseLine (line : String) : Command :=
  if let some pattern := line.dropPrefix? "search " then
    .search pattern.trimAscii.copy
  else if let some name := line.dropPrefix? "context " then
    .context name.trimAscii.copy
  else
    .query line

private partial def runInteractive (session : Session) (config : Config) : CoreM Unit := do
  let line := (← (← IO.getStdin).getLine).trimAscii.copy
  if line.isEmpty then return
  try
    runTimed session config (parseLine line)
  catch error =>
    let message ← error.toMessageData.toString
    if config.json then
      IO.println (Json.mkObj [("error", toJson message)]).compress
    else
      IO.eprintln s!"leanreach: {message}"
  (← IO.getStdout).flush
  runInteractive session config

private def validate (config : Config) : CliMainM Unit := do
  if config.depth > 8 then
    throw <| Lake.CliError.invalidOptArg "--depth" "an integer from 0 to 8"
  if config.limit == 0 || config.limit > 1000 then
    throw <| Lake.CliError.invalidOptArg "--limit" "an integer from 1 to 1000"

private unsafe def execute (config : Config) (command? : Option Command) : IO UInt32 := do
  let started ← IO.monoMsNow
  match command? with
  | some command =>
    let loadRelations := command matches .query _ | .context _
    withSessionFor config.root (commandNames config command) loadRelations fun session =>
      runTimed session config command
  | none =>
    withSession config.root fun session => runInteractive session config
  if config.profile then
    IO.eprintln s!"leanreach: elapsed={(← IO.monoMsNow) - started}ms"
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
      | ["context", name] => pure (some (.context name))
      | "cache" :: module :: modules =>
        pure (some (.cache <| (module :: modules).toArray.map (·.toName)))
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
