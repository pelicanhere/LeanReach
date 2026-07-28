import LeanReach
import Tests.Fixture

namespace LeanReach.Tests

open Lean

private def check (condition : Bool) (message : String) : CoreM Unit :=
  unless condition do throwError message

private unsafe def runTests : IO Unit :=
  withSession `Tests.Fixture fun session => do
    let result ← session.query "LeanReachFixture.double" (limit := 100)
    check result.target.file.isSome
      "local declaration has no source file"
    check (result.target.line == 5)
      "local declaration has the wrong source line"
    check (result.target.signature.contains ":=\n")
      "non-Prop declaration body is missing"
    check (result.target.signature.contains "n + n")
      "definition body was not pretty-printed with notation"
    check
      (result.upstream.any fun (_, declaration) => declaration.name == "HAdd.hAdd")
      "implementation-only upstream relation is missing"
    check
      (result.downstream.any fun (_, declaration) =>
        declaration.name == "LeanReachFixture.double_eq_add")
      "downstream relation is missing"

    let theoremResult ← session.query "LeanReachFixture.double_eq_add"
      (limit := 100) (downstream := false)
    check (theoremResult.target.signature.contains "n + n")
      "theorem signature was not pretty-printed with notation"
    check
      (theoremResult.upstream.any fun (_, declaration) =>
        declaration.name == "LeanReachFixture.double")
      "upstream relation is missing"

    let proofResult ← session.query "LeanReachFixture.double_zero_again"
      (limit := 100) (downstream := false)
    check
      (proofResult.upstream.any fun (_, declaration) =>
        declaration.name == "LeanReachFixture.double_zero")
      "proof-only upstream relation is missing"

    let usedResult ← session.query "LeanReachFixture.double_zero"
      (limit := 100) (upstream := false)
    check
      (usedResult.downstream.any fun (_, declaration) =>
        declaration.name == "LeanReachFixture.double_zero_again")
      "proof-only downstream relation is missing"

    let rankedResult ← session.query "LeanReachFixture.Topic.ranked"
      (limit := 100) (downstream := false)
    let some (_, first) := rankedResult.upstream[0]? |
      throwError "ranked dependencies are empty"
    check (first.name == "LeanReachFixture.Topic.nearby")
      "nearby dependency was not ranked first"

    let classResult ← session.query "Add" (upstream := false) (downstream := false)
    check (classResult.target.signature.contains "fields:")
      "class fields are missing"
    check (classResult.target.signature.contains "Add.add")
      "class field signature is missing"

    let searchResult ← session.search "double_eq" 10
    check
      (searchResult.any fun item =>
        item.name == "LeanReachFixture.double_eq_add")
      "local name search is missing"

    check (← session.search "LeanReachFixture.Color.noConfusion" 10).isEmpty
      "generated declaration was not blacklisted"
    check
      ((← session.search "LeanReachFixture.Box.value" 10).any fun item =>
        item.name == "LeanReachFixture.Box.value")
      "structure projection was blacklisted"

    let (_, context) ← session.context "LeanReachFixture.double_zero_again" 1 20
    let some first := context[0]? | throwError "ranked context is empty"
    check (first.declaration.name == "LeanReachFixture.double_zero")
      "proof dependency was not ranked first"
    let (_, expanded) ← session.context "LeanReachFixture.double_zero_again" 2 20
    check (expanded.any fun item => item.distance == 2)
      "ranked context was not expanded"

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
