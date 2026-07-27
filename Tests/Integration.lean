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

private def expectMissingField (label : String) (json : Json) (name : String) : IO Unit :=
  match json.getObjVal? name with
  | .error _ => pure ()
  | .ok _ => fail s!"{label}: obsolete response field '{name}' is still present"

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

  let removedMode ← runCli executable #["--mode=kernel", "Nat.gcd"]
  expectExit "removed kernel mode" 2 removedMode
  check (removedMode.stderr.contains "--mode") "removed --mode option was unexpectedly accepted"

private def testQuery (executable : System.FilePath) : IO Unit := do
  let output ← runCli executable #[
    "--module=Mathlib.Data.Nat.GCD.Basic",
    "--upstream",
    "-n=5",
    "Nat.gcd_comm",
    "--json"
  ]
  expectExit "query" 0 output
  let response ← parseJson output.stdout
  let target ← field Json response "target"
  check ((← field String target "name") == "Nat.gcd_comm") "query resolved the wrong target"
  let upstream ← field Json response "upstream"
  let items ← field (Array Json) upstream "items"
  check (items.size ≤ 5) "query ignored -n=5"

private def testSourceIndex (executable : System.FilePath) : IO Unit := do
  let args := #[
    "--module=Mathlib.Data.Nat.GCD.Basic",
    "--profile",
    "Nat.gcd",
    "--json"
  ]
  let first ← runCli executable args
  expectExit "source query" 0 first
  let response ← parseJson first.stdout
  let target ← field Json response "target"
  check ((← field String target "name") == "Nat.gcd") "source query resolved the wrong target"
  let source ← field Json target "source"
  let _ ← field String source "file"
  let _ ← field Nat source "line"
  check (first.stderr.contains "index=") "source profile omitted index timing"
  check (!first.stderr.contains "import=") "source query imported an Environment"

  let restored ← runCli executable args
  expectExit "restored source query" 0 restored
  check (restored.stderr.contains "source index restored:")
    "second source query did not restore the persistent index"

  let stats ← runCli executable #[
    "index",
    "--module=Mathlib.Data.Nat.GCD.Basic",
    "--json"
  ]
  expectExit "source index stats" 0 stats
  let statsJson ← parseJson stats.stdout
  check ((← field Nat statsJson "declarations") > 0) "source index contained no declarations"
  check ((← field Nat statsJson "relations") > 0) "source index contained no relations"

private def testInteractive (executable : System.FilePath) : IO Unit := do
  let input := "\n".intercalate [
    "",
    "{\"command\":\"search\",\"query\":\"gcd\"}",
    "{\"command\":\"query\",\"query\":\"Nat.gcd\",\"depth\":99}",
    "{\"command\":\"query\",\"query\":\"Nat.gcd\"}",
    "{\"command\":\"query\",\"query\":\"Nat.gcd\",\"direction\":\"upstream\",\"limit\":2}",
    "{\"command\":\"query\",\"query\":\"Nat.gcd\",\"direction\":7}",
    "{\"command\":\"ping\",\"query\":\"Nat.gcd\"}"
  ] ++ "\n"
  let output ← runCli executable #[
    "--interactive",
    "--module=Mathlib.Data.Nat.GCD.Basic",
    "--downstream",
    "--limit=1"
  ] (some input)
  expectExit "interactive" 0 output
  let lines := output.stdout.splitOn "\n"
    |>.filter (fun line => !line.trimAscii.isEmpty)
  check (lines.length == 6)
    s!"interactive: expected 6 responses, got {lines.length}\n{output.stdout}"
  let responses ← lines.mapM parseJson
  let some search := responses[0]? | fail "missing search response"
  let some invalidDepth := responses[1]? | fail "missing validation response"
  let some inherited := responses[2]? | fail "missing inherited-options response"
  let some overridden := responses[3]? | fail "missing overridden-options response"
  let some invalidDirection := responses[4]? | fail "missing typed-field response"
  let some removedCommand := responses[5]? | fail "missing removed-command response"

  check ((← field String search "query") == "gcd") "interactive search returned the wrong query"
  check ((← field (Array Json) search "items").size ≤ 1)
    "interactive search did not inherit the CLI limit"
  expectMissingField "interactive search" search "ok"
  expectMissingField "interactive search" search "result"

  let _ ← field String invalidDepth "error"
  let inheritedTarget ← field Json inherited "target"
  check ((← field String inheritedTarget "name") == "Nat.gcd")
    "session did not continue after an invalid request"
  let inheritedUpstream ← field Json inherited "upstream"
  check ((← field Nat inheritedUpstream "total") == 0)
    "interactive query did not inherit the CLI direction"

  let overriddenDownstream ← field Json overridden "downstream"
  check ((← field Nat overriddenDownstream "total") == 0)
    "interactive query did not apply its direction override"
  check ((← field (Array Json) (← field Json overridden "upstream") "items").size ≤ 2)
    "interactive query did not apply its limit override"

  let _ ← field String invalidDirection "error"
  let _ ← field String removedCommand "error"

def run : IO UInt32 := do
  try
    let executable ← leanreachPath
    check (← executable.pathExists) s!"LeanReach executable not found: {executable}"
    testParser executable
    testQuery executable
    testSourceIndex executable
    testInteractive executable
    IO.println "LeanReach CLI and NDJSON integration tests passed"
    return 0
  catch error =>
    IO.eprintln s!"LeanReach integration tests failed: {error}"
    return 1

end LeanReach.Tests.Integration

def main : IO UInt32 :=
  LeanReach.Tests.Integration.run
