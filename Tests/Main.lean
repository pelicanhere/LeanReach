import LeanReach
import Tests.Fixture
import Tests.PrivateA
import Tests.PrivateB

namespace LeanReach.Tests

open Lean

private def check (condition : Bool) (message : String) : CoreM Unit :=
  unless condition do throwError message

private unsafe def runTests : IO Unit := do
  let sourcePath ← unsafe prepareEnvironment
  let duplicateIndex := Index.build #[
    (`LeanReachFixture.a, `Tests.Fixture, ({} : NameSet).insert `LeanReachFixture.b),
    (`LeanReachFixture.a, `Tests.Fixture, ({} : NameSet).insert `LeanReachFixture.c),
    (`LeanReachFixture.b, `Tests.Fixture, {}),
    (`LeanReachFixture.c, `Tests.Fixture, {})
  ]
  unless duplicateIndex.size == 3 &&
      (duplicateIndex.upstream `LeanReachFixture.a 10).size == 2 do
    throw <| IO.userError "index did not merge duplicate declarations"
  let privateA := mkPrivateNameCore `Tests.PrivateA `LeanReachDuplicate.hidden
  let privateB := mkPrivateNameCore `Tests.PrivateB `LeanReachDuplicate.hidden
  let privateIndex := Index.build #[
    (privateA, `Tests.PrivateA, {}),
    (privateB, `Tests.PrivateB, {})
  ]
  let .error privateAmbiguity := privateIndex.resolve "LeanReachDuplicate.hidden" |
    throw <| IO.userError "duplicate private user names were not ambiguous"
  unless privateAmbiguity.contains "Tests.PrivateA" &&
      privateAmbiguity.contains "Tests.PrivateB" do
    throw <| IO.userError "private ambiguity omitted defining modules"
  let roots ← detectRoots
  unless roots.contains `Tests.Fixture do
    throw <| IO.userError "built local modules were not detected"
  unless roots.contains `Mathlib do
    throw <| IO.userError "required Mathlib was not detected"
  let localRoots := roots.filter (· != `Mathlib)
  unless localRoots == localRoots.qsort Name.lt do
    throw <| IO.userError "built local modules were not detected deterministically"
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
  let fixtureNames ← unsafe Cache.moduleNames `Tests.Fixture
  let hiddenTheorem :=
    mkPrivateNameCore `Tests.Fixture `LeanReachFixture.hidden_double_zero
  let hiddenDefinition :=
    mkPrivateNameCore `Tests.Fixture `LeanReachFixture.hiddenDouble
  let fixtureEnv ← importEnvironment #[`Tests.Fixture]
  let (planned, _) ← unsafe prettyPrintModuleIO sourcePath fixtureEnv
    `Tests.Fixture fixtureNames fixtureIndex.moduleOf?
  let (monolithic, _) ← unsafe ModuleData.withPrivateOverlay fixtureEnv
      `Tests.Fixture #[] fixtureNames fixtureIndex.moduleOf? fun env =>
    unsafe runCore (env.setMainModule `Tests.Fixture)
      (prettyPrintModule sourcePath `Tests.Fixture fixtureNames)
  unless fixtureNames.all fun name =>
      match planned.find? name, monolithic.find? name with
      | some left, some right => (toJson left).compress == (toJson right).compress
      | _, _ => false do
    throw <| IO.userError "planned PP changed declaration output"
  let some cachedWrapped := planned.find? `LeanReachFixture.cachedWrapped |
    throw <| IO.userError "irreducible definition is missing from planned PP"
  unless cachedWrapped.signature.contains "✝" do
    throw <| IO.userError "irreducible definition did not exercise dagger PP"
  let some cachedPrivateText := planned.find? `LeanReachFixture.cachedPrivateText |
    throw <| IO.userError "private text fixture is missing from planned PP"
  unless cachedPrivateText.signature.contains "_private." do
    throw <| IO.userError "private text fixture did not exercise cache text"
  unsafe Cache.savePPModule `Tests.Fixture planned
  let roundTripped ← unsafe Cache.loadPPModule `Tests.Fixture
  unless fixtureNames.all roundTripped.contains do
    throw <| IO.userError "PP cache dropped a freshly serialized declaration"
  let selected ← unsafe Cache.loadPP fixtureIndex.moduleOf?
    #[`LeanReachFixture.cachedWrapped]
  let some selectedWrapped := selected.find? `LeanReachFixture.cachedWrapped |
    throw <| IO.userError "selective PP cache load dropped an irreducible definition"
  unless (toJson selectedWrapped).compress == (toJson cachedWrapped).compress do
    throw <| IO.userError "selective PP cache load changed declaration output"
  let (withoutSource, _) ← unsafe runCore fixtureEnv <|
    prettyPrintModuleWithBodies `Tests.Fixture (none, {})
      #[`LeanReachFixture.double] {}
  let some withoutSource := withoutSource.find? `LeanReachFixture.double |
    throw <| IO.userError "declaration without source position is missing"
  unless withoutSource.line == 0 && withoutSource.column == 0 do
    throw <| IO.userError "missing source position did not remain 0:0"
  discard <| unsafe QueryCache.build #[`Tests.Fixture]
  for _ in [0:2] do
    let cachedRun ← unsafe withCachedQueryFor #[`Tests.Fixture]
        "LeanReachFixture.cachedWrapped" (Limits.uniform 0) fun session names => do
      check session.sourcePath.isEmpty
        "cached query unexpectedly prepared a source environment"
      check (!(← getEnv).contains `LeanReachFixture.cachedWrapped)
        "cached query unexpectedly imported its target module"
      let result ← session.describeQuery names
      check (result.target.signature.contains "✝")
        "cached query lost the serialized irreducible definition"
    unless cachedRun.isSome do
      throw <| IO.userError "irreducible definition did not use the query cache"
  let .ok (some cachedQuery) ← unsafe QueryCache.resolve #[`Tests.Fixture]
      "LeanReachFixture.Topic.ranked" |
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
  let .ok (some privateQuery) ← unsafe QueryCache.resolve #[`Tests.Fixture]
      "LeanReachFixture.hidden_double_zero" |
    throw <| IO.userError "private declaration did not resolve from its user name"
  unless privateQuery.target.name == hiddenTheorem do
    throw <| IO.userError "private query lost its kernel identity"
  let .error _ ← unsafe QueryCache.resolve #[`Tests.Fixture] "duplicateLeaf" |
    throw <| IO.userError "ambiguous short query was not rejected"
  let privateRoots := #[`Tests.PrivateA, `Tests.PrivateB]
  discard <| unsafe QueryCache.build privateRoots
  let .error cachedPrivateAmbiguity ← unsafe QueryCache.resolve privateRoots
      "LeanReachDuplicate.hidden" |
    throw <| IO.userError "cached duplicate private names were not ambiguous"
  unless cachedPrivateAmbiguity.contains "Tests.PrivateA" &&
      cachedPrivateAmbiguity.contains "Tests.PrivateB" do
    throw <| IO.userError "cached private ambiguity omitted defining modules"
  let .ok (some exactPrivate) ← unsafe QueryCache.resolve privateRoots
      privateA.toString |
    throw <| IO.userError "private kernel query key did not resolve"
  unless exactPrivate.target.name == privateA do
    throw <| IO.userError "private kernel query key resolved the wrong module"
  let some cachedSearch ← unsafe QueryCache.search #[`Tests.Fixture] "duplicateLeaf" 10 |
    throw <| IO.userError "complete leaf search did not use its shard"
  unless cachedSearch.map (·.name) == fixtureIndex.search "duplicateLeaf" 10 do
    throw <| IO.userError "cached leaf search changed search ordering"
  let some substringSearch ← unsafe QueryCache.search #[`Tests.Fixture]
      "doubleVia" 10 |
    throw <| IO.userError "substring search cache is missing"
  unless substringSearch.map (·.name) == fixtureIndex.search "doubleVia" 10 do
    throw <| IO.userError "cached substring search changed search ordering"
  let some missingSearch ← unsafe QueryCache.search #[`Tests.Fixture]
      "not_a_declaration_name" 10 |
    throw <| IO.userError "cached empty search fell back to the complete index"
  unless missingSearch.isEmpty do
    throw <| IO.userError "cached empty search returned a declaration"
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
  let some layeredSearch ← unsafe QueryCache.search layeredRoots
      "localization_maximal" 10 |
    throw <| IO.userError "base substring search did not use the overlay cache"
  unless layeredSearch.map (·.name) ==
      mathlibIndex.search "localization_maximal" 10 do
    throw <| IO.userError "overlay substring search changed search ordering"
  for (pattern, limit) in #[
      ("Submodule.span_le", 10),
      ("span_eq", 37),
      ("continuouson_image", 10),
      ("eq", 10)] do
    let some cached ← unsafe QueryCache.search #[`Mathlib] pattern limit |
      throw <| IO.userError s!"Mathlib search cache is missing for '{pattern}'"
    unless cached.map (·.name) == mathlibIndex.search pattern limit do
      throw <| IO.userError s!"cached search differs for '{pattern}'"
  let lazyRoots := #[`Tests.Main, `Tests.Fixture, `Mathlib]
  let .ok (some lazyLocal) ← unsafe QueryCache.resolve lazyRoots
      "LeanReachFixture.double" |
    throw <| IO.userError "query did not recover a missing local overlay"
  unless lazyLocal.target.name == `LeanReachFixture.double do
    throw <| IO.userError "recovered overlay resolved the wrong local declaration"
  unless lazyLocal.downstream.any (·.name == `LeanReachFixture.double_eq_add) do
    throw <| IO.userError "recovered overlay lost local reverse dependencies"
  withSession #[`Tests.Fixture] fun index session => do
    let fixtureNames ← unsafe Cache.moduleNames `Tests.Fixture
    check (fixtureNames.contains `LeanReachFixture.double)
      "module fragment is missing a source declaration"
    check (!fixtureNames.any (·.toString.contains "noConfusion"))
      "module fragment contains a generated declaration"
    check (fixtureNames.contains hiddenTheorem && fixtureNames.contains hiddenDefinition)
      "module fragment is missing a private declaration"
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

    let hiddenBodyResult ← session.query index "LeanReachFixture.hiddenDouble"
    check (hiddenBodyResult.target.name == hiddenDefinition.toString)
      "private definition lost its stable query name"
    check (hiddenBodyResult.target.line == 17)
      "private definition has the wrong source line"
    check (hiddenBodyResult.target.signature.contains ":=\n")
      "private definition body is missing"
    check (!hiddenBodyResult.target.signature.contains "_private" &&
        !hiddenBodyResult.target.signature.contains "✝")
      s!"private definition signature was not printed as a user name:\n\
        {hiddenBodyResult.target.signature}"
    check
      (hiddenBodyResult.downstream.any fun declaration =>
        declaration.name == "LeanReachFixture.doubleViaPrivate")
      "private definition downstream relation is missing"

    let hiddenTheoremResult ←
      session.query index "LeanReachFixture.hidden_double_zero" (Limits.uniform 100)
    check (hiddenTheoremResult.target.name == hiddenTheorem.toString)
      "private theorem lost its stable query name"
    check (hiddenTheoremResult.target.line == 13)
      "private theorem has the wrong source line"
    check (!hiddenTheoremResult.target.signature.contains ":=\n")
      "private theorem proof body was printed"
    check
      (hiddenTheoremResult.upstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double_zero")
      "private theorem proof dependency is missing"
    check
      (hiddenTheoremResult.downstream.any fun declaration =>
        declaration.name == "LeanReachFixture.double_zero_via_private")
      "private theorem downstream relation is missing"

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
        declaration.name == hiddenTheorem.toString)
      "private proof helper dependency is missing"

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
    check
      ((← session.search index "hidden_double" 10).any fun item =>
        item.name == hiddenTheorem.toString)
      "private name search is missing"

    check (← session.search index "LeanReachFixture.Color.noConfusion" 10).isEmpty
      "generated declaration was not blacklisted"
    check
      ((← session.search index "LeanReachFixture.Box.value" 10).any fun item =>
        item.name == "LeanReachFixture.Box.value")
      "structure projection was blacklisted"

  withInteractiveSession #[`Definitely.Missing] fun _ _ => pure ()
  withInteractiveSession #[`Tests.Fixture] fun session runner => do
    for query in #["double_eq", "double_zero_again"] do
      runner.search query 10 fun names => do
        check (!((← session.describeNames names).isEmpty))
          "interactive session search is missing"
    runner.query "LeanReachFixture.Topic.ranked" (Limits.uniform 1) fun names => do
        check ((← session.describeQuery names).upstream.size == 1)
          "interactive cached query is missing"

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
