import LeanReach
import Lake.CLI.Error
import Lake.Util.Cli

namespace LeanReach.Cli

open Lean

inductive Command where
  | lookup (pattern : String)
  | route (anchor wanted : String)
  | cache (modules : Array Name)
  | interactive

structure Config where
  root? : Option Name := none
  limits : Limits := {}
  routeDirection : RouteDirection := .consumers
  maxDepth : Nat := 3
  nodeBudget : Nat := 200
  beamWidth : Nat := 20
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

private def takeDirection : CliM RouteDirection := do
  match ← takeArg "--direction" with
  | "dependencies" => return .dependencies
  | "consumers" => return .consumers
  | _ => throw <| Lake.CliError.invalidOptArg "--direction" "'dependencies' or 'consumers'"

private def shortOption : Char → CliM PUnit
  | 'm' => do modifyThe Config ({ · with root? := some (← takeArg "-m").toName })
  | 'n' => do modifyThe Config ({ · with limits := Limits.uniform (← takeNat "-n") })
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
  | "--direction" => do
    modifyThe Config ({ · with routeDirection := ← takeDirection })
  | "--max-depth" => do
    modifyThe Config ({ · with maxDepth := ← takeNat "--max-depth" })
  | "--node-budget" => do
    modifyThe Config ({ · with nodeBudget := ← takeNat "--node-budget" })
  | "--beam-width" => do
    modifyThe Config ({ · with beamWidth := ← takeNat "--beam-width" })
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
  leanreach [OPTIONS] PATTERN
  leanreach [OPTIONS] route ANCHOR WANTED
  leanreach [OPTIONS] cache [MODULE...]
  leanreach [OPTIONS] --interactive

OPTIONS:
  -m, --module MODULE   override the detected local library or Mathlib root
  -n, --limit N         override result limits (default: 10 each)
  -i, --interactive     reuse one environment; read queries from stdin
  -j, --json            emit JSON (NDJSON in interactive mode)
      --direction DIR   route through consumers (default) or dependencies
      --max-depth N     route search depth (default: 3)
      --node-budget N   maximum declarations visited by a route (default: 200)
      --beam-width N    free-signature frontier width (default: 20)
      --profile         print elapsed and cache-stage time to stderr
  -h, --help            show this help

Without `--module`, combine built local lean_lib roots with required Mathlib.
With no modules, `cache` precomputes pretty-printed declarations for the detected view.
An exact declaration name shows dependencies; every other pattern is a regex search.
The `route` command finds a quoted declaration by shortest path, or guides a bounded
beam search with a Lean type. Interactive mode also accepts `route ANCHOR WANTED`.
"

private def printDeclaration (indent : String) (declaration : Declaration) : IO Unit := do
  let continuation := String.ofList (List.replicate indent.length ' ')
  IO.println <| indent ++ declaration.signature.replace "\n" ("\n" ++ continuation)
  IO.println s!"{indent}  {declaration.file.getD declaration.moduleName}:\
    {declaration.line}:{declaration.column}"

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

private def printRoute (json : Bool) (result : RouteResult) : IO Unit := do
  if json then
    IO.println (toJson result).compress
  else
    IO.println s!"routes ({result.results.size}, visited {result.visited}\
      {if result.truncated then ", budget exhausted" else ""})"
    if result.results.isEmpty then IO.println "  <none>"
    for (candidate, index) in result.results.zipIdx do
      printDeclaration s!"  [{index + 1}] " candidate.endpoint
      let score := candidate.signatureMatch
      IO.println s!"      match={score.kind.toString}, distance={candidate.distance}, \
        covered={score.coveredInputs}, obligations={score.extraObligations.size}"
      for step in candidate.path do
        let marker := step.edgeKind?.map (s!"      -[{·.toString}]-> ") |>.getD "      "
        IO.println s!"{marker}{step.declaration}"

private def printLookupNames (config : Config) (pattern : String)
    (session : Session) : LookupNames → IO Unit
  | .query names => do
    printQuery config.json (← session.describeQuery names)
  | .search names => do
    printSearch config.json pattern (← session.describeNames names)

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

private def withCacheProgress {α : Type} (json : Bool)
    (action : Cache.ProgressReporter → IO α) : IO α := do
  if json then return ← action Cache.ignoreProgress
  let display ← Cache.ProgressDisplay.create
  try
    action display.report
  finally
    display.finish

private def chompLine (line : String) : String :=
  (line.dropEndWhile fun char => char == '\n' || char == '\r').toString

private def parseInteractiveRoute (line : String) : Except String (Option (String × String)) :=
  let input := line.trimAscii.toString.toList
  let (command, afterCommand) := input.span fun char => !char.isWhitespace
  if String.ofList command != "route" then
    return none
  else
    let afterCommand := afterCommand.dropWhile (fun char => char.isWhitespace)
    let (anchor, afterAnchor) := afterCommand.span fun char => !char.isWhitespace
    let wanted := afterAnchor.dropWhile (fun char => char.isWhitespace)
    if anchor.isEmpty || wanted.isEmpty then
      throw "interactive route requires ANCHOR and WANTED"
    else
      return some (String.ofList anchor, String.ofList wanted)

private def runInteractive (session : Session) (runner : InteractiveRunner)
    (routeRunner : InteractiveRouteRunner) (config : Config) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  while true do
    let line := chompLine (← stdin.getLine)
    if line.trimAscii.isEmpty then break
    try
      match parseInteractiveRoute line with
      | .ok (some (anchor, wanted)) =>
        profiled config.profile "route" do
          let result ← routeRunner {
            anchor
            wanted
            direction := config.routeDirection
            maxDepth := config.maxDepth
            nodeBudget := config.nodeBudget
            beamWidth := config.beamWidth
            limit := config.limits.search
          }
          printRoute config.json result
      | .ok none => profiled config.profile "lookup" do
        runner line config.limits
          (printLookupNames config line session)
      | .error message => throw <| IO.userError message
    catch error =>
      let message := toString error
      if config.json then
        IO.println (Json.mkObj [("error", toJson message)]).compress
      else
        IO.eprintln s!"leanreach: {message}"
    stdout.flush

private def validate (config : Config) : CliMainM Unit := do
  if config.limits.search == 0 || config.limits.search > 1000 then
    throw <| Lake.CliError.invalidOptArg "--limit" "an integer from 1 to 1000"
  if config.nodeBudget == 0 || config.nodeBudget > 100000 then
    throw <| Lake.CliError.invalidOptArg
      "--node-budget" "an integer from 1 to 100000"
  if config.beamWidth == 0 || config.beamWidth > 10000 then
    throw <| Lake.CliError.invalidOptArg
      "--beam-width" "an integer from 1 to 10000"

private unsafe def Config.roots (config : Config) (refresh := false) : IO (Array Name) :=
  config.root?.map (#[·]) |>.getDM (detectRoots refresh)

private unsafe def execute (config : Config) (command : Command) : IO UInt32 := do
  match command with
  | .cache modules =>
    profiled config.profile "cache" do
      if modules.isEmpty then
        let (roots, result) ← withCacheProgress config.json fun progress => do
          progress.count .detectingProject 0 1
          let roots ← config.roots true
          progress.count .detectingProject 1 1
          return (roots, ← buildPPRoots roots progress)
        printPP config roots result
      else
        let result ← withCacheProgress config.json fun progress =>
          buildPPModules modules progress
        printPP config modules result
  | .lookup pattern =>
    profiled config.profile "lookup" do
      let roots ← config.roots
      withLookupFor roots pattern config.limits
        (printLookupNames config pattern)
  | .route anchor wanted =>
    profiled config.profile "route" do
      let result ← routeFor (← config.roots) {
        anchor
        wanted
        direction := config.routeDirection
        maxDepth := config.maxDepth
        nodeBudget := config.nodeBudget
        beamWidth := config.beamWidth
        limit := config.limits.search
      }
      printRoute config.json result
  | .interactive =>
    withInteractiveSession (← config.roots) fun session runner routeRunner =>
      runInteractive session runner routeRunner config
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
      if arguments.isEmpty then pure .interactive
      else throw <| Lake.CliError.unexpectedArguments arguments.toList
    else
      match arguments.toList with
      | "cache" :: modules => pure (.cache <| modules.toArray.map (·.toName))
      | ["route", anchor, wanted] => pure (.route anchor wanted)
      | [pattern] => pure (.lookup pattern)
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
