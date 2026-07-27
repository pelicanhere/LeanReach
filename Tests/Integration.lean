import Lean.Data.Json

open Lean

namespace LeanReach.Tests.Integration

private def fail {α : Type} (message : String) : IO α :=
  throw <| IO.userError message

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    fail message

private def parseJson (text : String) : IO Json :=
  match Json.parse text with
  | .ok json => pure json
  | .error message => fail s!"invalid JSON response: {message}\n{text}"

private def field (α : Type) [FromJson α] (json : Json) (name : String) : IO α :=
  match json.getObjValAs? α name with
  | .ok value => pure value
  | .error message => fail s!"invalid response field '{name}': {message}\n{json.compress}"

private def leanreachPath : IO System.FilePath := do
  let some binDir := (← IO.appPath).parent |
    fail "integration test executable has no parent directory"
  let executable := (binDir / "leanreach").addExtension System.FilePath.exeExtension
  unless ← executable.pathExists do
    let build ← IO.Process.output { cmd := "lake", args := #["build", "leanreach"] }
    check (build.exitCode == 0)
      s!"failed to build LeanReach before integration tests:\n{build.stderr}"
  return executable

private def runCli (executable : System.FilePath) (args : Array String)
    (input? : Option String := none) : IO IO.Process.Output :=
  IO.Process.output { cmd := executable.toString, args } input?

private def expectExit (label : String) (expected : UInt32) (output : IO.Process.Output) :
    IO Unit :=
  check (output.exitCode == expected)
    s!"{label}: expected exit {expected}, got {output.exitCode}\nstdout:\n{output.stdout}\nstderr:\n{output.stderr}"

private def testParser (executable : System.FilePath) : IO Unit := do
  let help ← runCli executable #["--help"]
  expectExit "help" 0 help
  check (help.stdout.contains "USAGE:") "help output omitted usage"

  let empty ← runCli executable #[]
  expectExit "empty command" 2 empty
  check (empty.stderr.contains "no declaration") "empty command returned the wrong diagnostic"

  let conflict ← runCli executable #["--interactive", "Nat.gcd"]
  expectExit "command conflict" 2 conflict
  check (conflict.stderr.contains "only one query") "command conflict was not rejected by parser"

  let missing ← runCli executable #["--module"]
  expectExit "missing module" 2 missing
  check (missing.stderr.contains "missing module name") "missing module returned the wrong diagnostic"

private def testQuery (executable : System.FilePath) : IO Unit := do
  let output ← runCli executable #[
    "--module=Mathlib.Data.Nat.GCD.Basic",
    "--mode=kernel",
    "--upstream",
    "-n=5",
    "Nat.gcd_comm",
    "--json"
  ]
  expectExit "query" 0 output
  let response ← parseJson output.stdout
  let target ← field Json response "target"
  check ((← field String target "name") == "Nat.gcd_comm") "query resolved the wrong target"
  check ((← field String response "mode") == "kernel") "query ignored --mode=kernel"
  let upstream ← field Json response "upstream"
  let items ← field (Array Json) upstream "items"
  check (items.size ≤ 5) "query ignored -n=5"

private def testInteractive (executable : System.FilePath) : IO Unit := do
  let input := "\n".intercalate [
    "{\"id\":1,\"command\":\"ping\",\"depth\":\"ignored\"}",
    "{\"id\":2,\"command\":\"search\",\"query\":\"gcd\",\"direction\":7,\"limit\":2}",
    "{\"id\":{\"suite\":\"validation\"},\"command\":\"query\",\"query\":\"Nat.gcd\",\"depth\":99}",
    "{\"id\":4,\"command\":\"unknown\"}",
    "{\"id\":5,\"command\":\"quit\"}"
  ] ++ "\n"
  let output ← runCli executable #[
    "--interactive",
    "--module=Mathlib.Data.Nat.GCD.Basic"
  ] (some input)
  expectExit "interactive" 0 output
  let lines := output.stdout.splitOn "\n"
    |>.filter (fun line => !line.trimAscii.isEmpty)
  check (lines.length == 5)
    s!"interactive: expected 5 responses, got {lines.length}\n{output.stdout}"
  let responses ← lines.mapM parseJson
  let some ping := responses[0]? | fail "missing ping response"
  let some search := responses[1]? | fail "missing search response"
  let some invalid := responses[2]? | fail "missing validation response"
  let some unknown := responses[3]? | fail "missing unknown-command response"
  let some quit := responses[4]? | fail "missing quit response"
  check (← field Bool ping "ok") "ping rejected an unrelated malformed field"
  check (← field Bool search "ok") "search rejected an unrelated malformed field"
  check (!(← field Bool invalid "ok")) "invalid depth unexpectedly succeeded"
  let invalidId ← field Json invalid "id"
  check ((← field String invalidId "suite") == "validation")
    "validation error did not preserve its object id"
  check (!(← field Bool unknown "ok")) "unknown command unexpectedly succeeded"
  check ((← field Nat unknown "id") == 4) "unknown command did not preserve its scalar id"
  check (← field Bool quit "ok") "quit failed"

def run : IO UInt32 := do
  try
    let executable ← leanreachPath
    check (← executable.pathExists) s!"LeanReach executable not found: {executable}"
    testParser executable
    testQuery executable
    testInteractive executable
    IO.println "LeanReach CLI and NDJSON integration tests passed"
    return 0
  catch error =>
    IO.eprintln s!"LeanReach integration tests failed: {error}"
    return 1

end LeanReach.Tests.Integration

def main : IO UInt32 :=
  LeanReach.Tests.Integration.run
