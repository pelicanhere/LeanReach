import LeanReach.Query
import LeanReach.SourceIndex

namespace LeanReach.Tests

open Lean Lean.Core

private def check (condition : Bool) (message : String) : CoreM Unit :=
  unless condition do
    throwError message

private def expectQuery (result : Except QueryFailure QueryResult) : CoreM QueryResult :=
  match result with
  | .ok result => pure result
  | .error failure => throwError failure.error

private def sourceTests : CoreM Unit := do
  let result ← expectQuery (← runQuery "Nat.gcd" {
    mode := .source
    direction := .both
    depth := 1
    limit := 1000
  })
  check (result.target.name == "Nat.gcd") "source query resolved the wrong declaration"
  check result.target.source.file.isSome "source query did not resolve the target file"
  check result.target.source.line.isSome "source query did not resolve the target line"
  check
    (result.upstream.items.any fun relation =>
      relation.declaration.name == "Nat.mod_lt")
    "source query omitted the direct Nat.mod_lt dependency"
  check
    (result.downstream.items.any fun relation =>
      relation.declaration.name == "Nat.gcd_comm")
    "source query omitted the direct Nat.gcd_comm dependent"

  match ← runQuery "gcd_comm" {
    mode := .source
    direction := .both
    depth := 0
    limit := 20
  } with
  | .ok _ => throwError "ambiguous suffix unexpectedly resolved to one declaration"
  | .error failure =>
    check (failure.candidates.size >= 2) "ambiguous suffix returned too few candidates"
    check
      (failure.candidates.any fun declaration =>
        declaration.name == "Nat.gcd_comm")
      "ambiguous suffix omitted Nat.gcd_comm"
    check
      (failure.candidates.any fun declaration =>
        declaration.name == "Int.gcd_comm")
      "ambiguous suffix omitted Int.gcd_comm"

  let search ← runSearch "gcd_comm" { limit := 20 }
  check (search.total >= 2) "name search returned too few matches"
  check
    (search.items.any fun declaration => declaration.name == "Nat.gcd_comm")
    "name search omitted Nat.gcd_comm"

  let generated := "StateCpsT.instMonadStateOf.match_1"
  match ← runQuery generated {
    mode := .source
    direction := .both
    depth := 0
    limit := 20
  } with
  | .ok _ => throwError "exact generated name bypassed the internal declaration filter"
  | .error _ => pure ()
  let generatedResult ← expectQuery (← runQuery generated {
    mode := .source
    direction := .both
    depth := 0
    limit := 20
    includeInternal := true
  })
  check
    (generatedResult.target.name == generated)
    "includeInternal did not restore exact generated-name resolution"

private unsafe def sourceIndexTests : CoreM Unit := do
  let roots := #["Mathlib.Data.Nat.GCD.Basic".toName]
  let index ← SourceIndex.build roots
  let sourcePath ← Query.sourceSearchPath
  let result ← match ← SourceIndex.runQuery index sourcePath "Nat.gcd" {
      direction := .both
      depth := 1
      limit := 1000
    } with
    | .ok result => pure result
    | .error failure => throwError failure.error
  check (result.target.name == "Nat.gcd") "source index resolved the wrong declaration"
  check result.target.source.file.isSome "source index did not resolve the target file"
  check result.target.source.line.isSome "source index did not resolve the target line"
  check
    (result.upstream.items.any fun relation =>
      relation.declaration.name == "Nat.mod_lt")
    "source index omitted the direct Nat.mod_lt dependency"
  check
    (result.downstream.items.any fun relation =>
      relation.declaration.name == "Nat.gcd_comm")
    "source index omitted the direct Nat.gcd_comm dependent"

  let search ← SourceIndex.runSearch index sourcePath "gcd_comm" { limit := 20 }
  check (search.total >= 2) "source index name search returned too few matches"
  check
    (search.items.any fun declaration => declaration.name == "Nat.gcd_comm")
    "source index name search omitted Nat.gcd_comm"

  let _ ← unsafe SourceIndex.withIndex roots fun cached =>
    pure cached.declarationCount
  let restored? ← IO.mkRef false
  let cachedCount ← unsafe SourceIndex.withIndex roots
    (fun cached => pure cached.declarationCount)
    (fun message =>
      if message.startsWith "source index restored:" then
        restored?.set true
      else
        pure ())
  check (cachedCount > 0) "restored source index was empty"
  check (← restored?.get) "source index cache was not restored on the second load"

private def kernelTests : CoreM Unit := do
  let result ← expectQuery (← runQuery "Nat.gcd_comm" {
    mode := .kernel
    direction := .upstream
    depth := 1
    limit := 100
  })
  check (result.mode == "kernel") "kernel query reported the wrong mode"
  check (result.upstream.total > 0) "kernel query returned no upstream dependencies"
  check
    (result.upstream.items.any fun relation =>
      relation.declaration.name == "Nat.gcd")
    "kernel query omitted the Nat.gcd constant"

private unsafe def runWithEnvironment (level : OLeanLevel) (action : CoreM Unit) : IO Unit := do
  let imports : Array Import := #["Mathlib.Data.Nat.GCD.Basic".toName].map
    ({ module := · })
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := false) (level := level)
  try
    CoreM.toIO' action
      { fileName := "<leanreach-tests>", fileMap := default }
      { env }
  finally
    env.freeRegions

unsafe def run : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    runWithEnvironment .server (sourceTests *> sourceIndexTests)
    runWithEnvironment .private kernelTests
    IO.println "LeanReach semantic smoke tests passed"
    return 0
  catch error =>
    IO.eprintln s!"LeanReach semantic smoke tests failed: {error}"
    return 1

end LeanReach.Tests

unsafe def main : IO UInt32 :=
  LeanReach.Tests.run
