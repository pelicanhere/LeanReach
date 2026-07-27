import Lake.CLI.Error
import Lake.Util.Cli
import LeanReach.Cli

namespace LeanReach.Cli

private abbrev CliMainM := ExceptT Lake.CliError IO
private abbrev CliStateM := StateT Config CliMainM
private abbrev CliM := Lake.ArgsT CliStateM

private def failWith {α : Type} : Except String α → CliM α
  | .ok value => pure value
  | .error message => throw <| .invalidEnv message

private def takeOptionArg (option expected : String) : CliM String := do
  let some value ← Lake.takeArg? |
    throw <| .missingOptArg option expected
  return value

private def setCommand (command : Command) : CliM PUnit := do
  if (← getThe Config).command.isSome then
    throw <| .invalidEnv "only one query, search, index, or interactive mode may be provided"
  modifyThe Config fun config => { config with command := some command }

private def addImport (option : String) : CliM PUnit := do
  let moduleName ← takeOptionArg option "module name"
  modifyThe Config fun config =>
    { config with imports := config.imports.push moduleName.toName }

private def setMode (option : String) : CliM PUnit := do
  let mode ← failWith <| parseDependencyMode option (← takeOptionArg option "source or kernel")
  modifyThe Config fun config => { config with mode }

private def setDirection (option : String) : CliM PUnit := do
  let direction ← failWith <|
    parseDirection option (← takeOptionArg option "both, upstream, or downstream")
  modifyThe Config fun config => { config with direction }

private def setDepth (option : String) : CliM PUnit := do
  let depth ← failWith <| parseDepth option (← takeOptionArg option "integer from 0 to 8")
  modifyThe Config fun config => { config with depth }

private def setLimit (option : String) : CliM PUnit := do
  let limit ← failWith <| parseLimit option (← takeOptionArg option "integer from 1 to 1000")
  modifyThe Config fun config => { config with limit }

private def shortOption : Char → CliM PUnit
  | 'm' => addImport "-m"
  | 'd' => setDepth "-d"
  | 'n' => setLimit "-n"
  | 'j' => modifyThe Config ({ · with json := true })
  | 'h' => modifyThe Config ({ · with help := true })
  | option => throw <| .unknownShortOption option

private def longOption : String → CliM PUnit
  | "--module" => addImport "--module"
  | "--import" => addImport "--import"
  | "--mode" => setMode "--mode"
  | "--direction" => setDirection "--direction"
  | "--depth" => setDepth "--depth"
  | "--limit" => setLimit "--limit"
  | "--upstream" => modifyThe Config ({ · with direction := .upstream })
  | "--downstream" => modifyThe Config ({ · with direction := .downstream })
  | "--json" => modifyThe Config ({ · with json := true })
  | "--interactive" => setCommand .interactive
  | "--include-internal" => modifyThe Config ({ · with includeInternal := true })
  | "--profile" => modifyThe Config ({ · with profile := true })
  | "--help" => modifyThe Config ({ · with help := true })
  | "--version" => modifyThe Config ({ · with version := true })
  | option => throw <| .unknownLongOption option

private def cliOption : String → CliM PUnit :=
  Lake.option {
    short := shortOption
    long := longOption
    longShort := fun option => throw <| .unknownLongOption option
  }

private def parsePositionals : List String → CliM PUnit
  | [] => pure ()
  | ["query"] => throw <| .missingArg "declaration after query"
  | ["search"] => throw <| .missingArg "pattern after search"
  | ["index"] => setCommand .index
  | ["query", declaration] => setCommand (.query declaration)
  | ["search", pattern] => setCommand (.search pattern)
  | [declaration] => setCommand (.query declaration)
  | arguments => throw <| .unexpectedArguments arguments

private def parse : CliM Config := do
  Lake.processOptions cliOption
  parsePositionals (← Lake.takeArgs)
  getThe Config

private def parseArgs (args : List String) : IO (Except Lake.CliError Config) :=
  ((parse.run' args).run' {}).run

unsafe def main (args : List String) : IO UInt32 := do
  match ← parseArgs args with
  | .ok config => run config
  | .error error =>
    IO.eprintln s!"leanreach: {error}"
    IO.eprintln "Try 'leanreach --help'."
    return 2

end LeanReach.Cli

unsafe def main (args : List String) : IO UInt32 :=
  LeanReach.Cli.main args
