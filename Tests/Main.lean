import LeanReach
import Tests.Fixture

namespace LeanReach.Tests

open Lean

private def check (condition : Bool) (message : String) : CoreM Unit :=
  unless condition do throwError message

private unsafe def runTests : IO Unit := do
  let roots ← detectRoots
  unless roots.contains `Tests.Fixture do
    throw <| IO.userError "built local modules were not detected"
  unless roots.contains `Mathlib do
    throw <| IO.userError "required Mathlib was not detected"
  withSession #[`Tests.Fixture] fun session => do
    let fixtureNames ← unsafe Cache.moduleNames `Tests.Fixture
    check (fixtureNames.contains `LeanReachFixture.double)
      "module fragment is missing a source declaration"
    check (!fixtureNames.any (·.toString.contains "noConfusion"))
      "module fragment contains a generated declaration"
    check (!fixtureNames.any isPrivateName)
      "module fragment contains a private declaration"
    let result ← session.query "LeanReachFixture.double" (Limits.uniform 100)
    check result.target.file.isSome
      "local declaration has no source file"
    check (result.target.line == 5)
      "local declaration has the wrong source line"
    check (result.target.signature.contains ":=\n")
      "non-Prop declaration body is missing"
    check (result.target.signature.contains "n + n")
      "definition body was not pretty-printed with notation"
    check (result.upstream.any fun declaration => declaration.name == "HAdd.hAdd")
      "implementation-only upstream relation is missing"
    check
      (result.downstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double_eq_add")
      "downstream relation is missing"

    let privateBodyResult ← session.query "LeanReachFixture.doubleViaPrivate"
    check (privateBodyResult.target.signature.contains "hiddenDouble")
      "definition body through a private constant was not pretty-printed"

    let theoremResult ← session.query "LeanReachFixture.double_eq_add" (Limits.uniform 100)
    check (theoremResult.target.signature.contains "n + n")
      "theorem signature was not pretty-printed with notation"
    check
      (theoremResult.upstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double")
      "upstream relation is missing"

    let proofResult ← session.query "LeanReachFixture.double_zero_again" (Limits.uniform 100)
    check
      (proofResult.upstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double_zero")
      "proof-only upstream relation is missing"

    let usedResult ← session.query "LeanReachFixture.double_zero" (Limits.uniform 100)
    check
      (usedResult.downstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double_zero_again")
      "proof-only downstream relation is missing"
    check
      (usedResult.downstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double_zero_via_private")
      "dependency through a private proof helper is missing"

    let rankedResult ← session.query "LeanReachFixture.Topic.ranked" (Limits.uniform 1)
    check (rankedResult.upstream.size == 1)
      "dependency limit was not applied during ranking"
    let some first := rankedResult.upstream[0]? |
      throwError "ranked dependencies are empty"
    check (first.name == "LeanReachFixture.Topic.nearby")
      "nearby dependency was not ranked first"

    let classResult ← session.query "Add"
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

  withLazySession #[`Tests.Fixture] fun session run => do
    for query in #["double_eq", "double_zero_again"] do
      run (fun index =>
        let names := index.search query 10
        pure (names, names)) fun names => do
        check (!((← session.describeNames names).isEmpty))
          "lazy session search is missing"
    run (fun index => do
      let names ← index.queryNames "LeanReachFixture.Topic.ranked" (Limits.uniform 1)
      pure (names, names.all)) fun names => do
        check ((← session.describeQuery names).upstream.size == 1)
          "prepared lazy query is missing"

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
