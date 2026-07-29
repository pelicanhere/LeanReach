import LeanReach
import Tests.Fixture

namespace LeanReach.Tests

open Lean

private def check (condition : Bool) (message : String) : CoreM Unit :=
  unless condition do throwError message

private unsafe def runTests : IO Unit := do
  discard <| unsafe prepareEnvironment
  let duplicateIndex := Index.build #[
    (`LeanReachFixture.a, `Tests.Fixture, ({} : NameSet).insert `LeanReachFixture.b),
    (`LeanReachFixture.a, `Tests.Fixture, ({} : NameSet).insert `LeanReachFixture.c),
    (`LeanReachFixture.b, `Tests.Fixture, {}),
    (`LeanReachFixture.c, `Tests.Fixture, {})
  ]
  unless duplicateIndex.size == 3 &&
      (duplicateIndex.upstream `LeanReachFixture.a 10).size == 2 do
    throw <| IO.userError "index did not merge duplicate declarations"
  let roots ← detectRoots
  unless roots.contains `Tests.Fixture do
    throw <| IO.userError "built local modules were not detected"
  unless roots.contains `Mathlib do
    throw <| IO.userError "required Mathlib was not detected"
  let mathlibIndex ← unsafe Cache.loadIndex #[`Mathlib] true
  let intervalRank := mathlibIndex.upstream
    `ContinuousOn.image_Icc_of_antitoneOn 10
  unless intervalRank.take 2 ==
      #[`intermediate_value_Icc', `AntitoneOn.image_Icc_subset] do
    throw <| IO.userError "interval proof dependencies are poorly ranked"
  let spanRank := mathlibIndex.upstream `Submodule.span_eq_bot 10
  unless spanRank.take 2 == #[`Submodule.span_le, `Submodule.subset_span] do
    throw <| IO.userError "span proof dependencies are poorly ranked"
  let pidRank := mathlibIndex.upstream
    `isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal 10
  for expected in #[
      `IsNoetherianRing.of_isLocalization_maximal,
      `IsIntegrallyClosed.of_isLocalization_maximal,
      `Ring.krullDimLE_of_isLocalization_maximal,
      `IsPrincipalIdealRing.of_finite_maximals] do
    unless pidRank.contains expected do
      throw <| IO.userError s!"PID proof dependency '{expected}' is poorly ranked"
  let fixtureIndex ← unsafe Cache.loadIndex #[`Tests.Fixture] true
  discard <| unsafe QueryCache.build #[`Tests.Fixture]
  let some cachedQuery ← unsafe QueryCache.load #[`Tests.Fixture]
      `LeanReachFixture.Topic.ranked |
    throw <| IO.userError "exact query cache is missing"
  let .ok expectedQuery :=
      fixtureIndex.queryNames "LeanReachFixture.Topic.ranked" {} |
    throw <| IO.userError "fixture query is missing"
  unless cachedQuery.queryNames {} == expectedQuery do
    throw <| IO.userError "cached query does not preserve ranking"
  let .ok (some shortQuery) ← unsafe QueryCache.resolve #[`Tests.Fixture]
      "doubleViaPrivate" |
    throw <| IO.userError "unique short query did not resolve from its shard"
  unless shortQuery.target.name == `LeanReachFixture.doubleViaPrivate do
    throw <| IO.userError "short query resolved to the wrong declaration"
  let .error _ ← unsafe QueryCache.resolve #[`Tests.Fixture] "duplicateLeaf" |
    throw <| IO.userError "ambiguous short query was not rejected"
  let some cachedSearch ← unsafe QueryCache.search #[`Tests.Fixture] "duplicateLeaf" 10 |
    throw <| IO.userError "complete leaf search did not use its shard"
  unless cachedSearch.map (·.name) == fixtureIndex.search "duplicateLeaf" 10 do
    throw <| IO.userError "cached leaf search changed search ordering"
  if (← unsafe QueryCache.search #[`Tests.Fixture] "doubleVia" 10).isSome then
    throw <| IO.userError "substring search incorrectly used a single name shard"
  let layeredRoots := #[`Tests.Fixture, `Mathlib]
  discard <| unsafe QueryCache.build layeredRoots
  let some overlay ← unsafe QueryOverlay.load layeredRoots |
    throw <| IO.userError "local query overlay is missing"
  unless overlay.baseRoot == `Mathlib && overlay.size > 0 do
    throw <| IO.userError "local query overlay has the wrong base or no declarations"
  let .ok (some layeredLocal) ← unsafe QueryCache.resolve layeredRoots
      "doubleViaPrivate" |
    throw <| IO.userError "local declaration did not resolve through the overlay"
  unless layeredLocal.target.name == `LeanReachFixture.doubleViaPrivate do
    throw <| IO.userError "overlay resolved the wrong local declaration"
  let .ok (some layeredRelations) ← unsafe QueryCache.resolve layeredRoots
      "LeanReachFixture.double" |
    throw <| IO.userError "local overlay relations are missing"
  unless layeredRelations.downstream.any
      (·.name == `LeanReachFixture.double_eq_add) do
    throw <| IO.userError "local overlay downstream relation is missing"
  let .ok (some layeredBase) ← unsafe QueryCache.resolve layeredRoots
      "Submodule.span_le" |
    throw <| IO.userError "base declaration did not resolve through the overlay"
  unless layeredBase.target.name == `Submodule.span_le do
    throw <| IO.userError "overlay resolved the wrong base declaration"
  withSession #[`Tests.Fixture] fun index session => do
    let fixtureNames ← unsafe Cache.moduleNames `Tests.Fixture
    check (fixtureNames.contains `LeanReachFixture.double)
      "module fragment is missing a source declaration"
    check (!fixtureNames.any (·.toString.contains "noConfusion"))
      "module fragment contains a generated declaration"
    check (!fixtureNames.any isPrivateName)
      "module fragment contains a private declaration"
    let result ← session.query index "LeanReachFixture.double" (Limits.uniform 100)
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

    let privateBodyResult ← session.query index "LeanReachFixture.doubleViaPrivate"
    check (privateBodyResult.target.signature.contains "hiddenDouble")
      "definition body through a private constant was not pretty-printed"

    let theoremResult ← session.query index "LeanReachFixture.double_eq_add" (Limits.uniform 100)
    check (theoremResult.target.signature.contains "n + n")
      "theorem signature was not pretty-printed with notation"
    check
      (theoremResult.upstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double")
      "upstream relation is missing"

    let proofResult ← session.query index "LeanReachFixture.double_zero_again" (Limits.uniform 100)
    check
      (proofResult.upstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double_zero")
      "proof-only upstream relation is missing"

    let usedResult ← session.query index "LeanReachFixture.double_zero" (Limits.uniform 100)
    check
      (usedResult.downstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double_zero_again")
      "proof-only downstream relation is missing"
    check
      (usedResult.downstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double_zero_via_private")
      "dependency through a private proof helper is missing"

    let rankedResult ← session.query index "LeanReachFixture.Topic.ranked" (Limits.uniform 1)
    check (rankedResult.upstream.size == 1)
      "dependency limit was not applied during ranking"
    let some first := rankedResult.upstream[0]? |
      throwError "ranked dependencies are empty"
    check (first.name == "LeanReachFixture.Topic.nearby")
      "nearby dependency was not ranked first"

    let classResult ← session.query index "Add"
    check (classResult.target.signature.contains "fields:")
      "class fields are missing"
    check (classResult.target.signature.contains "Add.add")
      "class field signature is missing"

    let searchResult ← session.search index "double_eq" 10
    check
      (searchResult.any fun item =>
        item.name == "LeanReachFixture.double_eq_add")
      "local name search is missing"

    check (← session.search index "LeanReachFixture.Color.noConfusion" 10).isEmpty
      "generated declaration was not blacklisted"
    check
      ((← session.search index "LeanReachFixture.Box.value" 10).any fun item =>
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
