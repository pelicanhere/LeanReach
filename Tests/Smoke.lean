import LeanReach.SourceIndex

namespace LeanReach.Tests

open Lean

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw <| IO.userError message

private def expectQuery (result : Except QueryFailure QueryResult) : IO QueryResult :=
  match result with
  | .ok result => pure result
  | .error failure => throw <| IO.userError failure.error

private unsafe def sourceIndexTests : IO Unit := do
  let roots := #["Mathlib.Data.Nat.GCD.Basic".toName]
  let index ← SourceIndex.build roots
  let sourcePath ← Query.sourceSearchPath
  let result ← expectQuery (← SourceIndex.runQuery index sourcePath "Nat.gcd" {
      direction := .both
      depth := 1
      limit := 1000
    })
  check (result.target.name == "Nat.gcd") "source index resolved the wrong declaration"
  check result.target.source.file.isSome "source index did not resolve the target file"
  check (!result.target.source.moduleName.isEmpty) "source index did not resolve the target module"
  check (result.target.source.line > 0) "source index returned a zero source line"
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

  let rejectedMissing ←
    try
      let _ ← SourceIndex.build #["LeanReach.Tests.MissingIleanFixture".toName]
      pure false
    catch _ =>
      pure true
  check rejectedMissing "source index accepted a closure with a missing .ilean"

unsafe def run : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    unsafe sourceIndexTests
    IO.println "LeanReach semantic smoke tests passed"
    return 0
  catch error =>
    IO.eprintln s!"LeanReach semantic smoke tests failed: {error}"
    return 1

end LeanReach.Tests

unsafe def main : IO UInt32 :=
  LeanReach.Tests.run
