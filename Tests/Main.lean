import LeanReach
import Tests.Fixture

namespace LeanReach.Tests

open Lean

private def check (condition : Bool) (message : String) : CoreM Unit :=
  unless condition do throwError message

private unsafe def runTests : IO Unit :=
  withSession `Tests.Fixture fun session => do
    let result ← session.query "LeanReachFixture.double" { limit := 100 }
    check result.target.source.file.isSome
      "local declaration has no source file"
    check (result.target.source.line == 5)
      "local declaration has the wrong source line"
    check
      (result.downstream.any fun item =>
        item.declaration.name == "LeanReachFixture.double_eq_add")
      "downstream relation is missing"

    let theoremResult ← session.query "LeanReachFixture.double_eq_add" {
      downstream := false
      limit := 100
    }
    check (theoremResult.target.signature.contains "n + n")
      "theorem signature was not pretty-printed with notation"
    check
      (theoremResult.upstream.any fun item =>
        item.declaration.name == "LeanReachFixture.double")
      "upstream relation is missing"

    let searchResult ← session.search "double_eq" 10
    check
      (searchResult.items.any fun item =>
        item.name == "LeanReachFixture.double_eq_add")
      "local name search is missing"

unsafe def main : IO UInt32 := do
  try
    unsafe runTests
    IO.println "LeanReach tests passed"
    return 0
  catch error =>
    IO.eprintln s!"LeanReach tests failed: {error}"
    return 1

end LeanReach.Tests

unsafe def main : IO UInt32 :=
  LeanReach.Tests.main
