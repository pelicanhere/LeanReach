import Tests.Fixture
import Tests.PrivateA
import Tests.PrivateB
import Tests.Support

namespace LeanReach.Tests.Integration

open Lean Meta

unsafe def run : IO Unit := do
  let sourcePath ← unsafe prepareEnvironment
  unless (← sourcePath.findModuleWithExt "lean" `Tests.Fixture).isSome do
    throw <| IO.userError s!"project source path does not contain Tests.Fixture: {sourcePath}"
  unless (← sourcePath.findModuleWithExt "lean" `Lake.Config.Module).isSome do
    throw <| IO.userError "project source path does not contain Lake.Config.Module"
  let duplicateIndex := Index.build #[
    (`LeanReachFixture.a, `Tests.Fixture, ({} : NameSet).insert `LeanReachFixture.b),
    (`LeanReachFixture.a, `Tests.Fixture, ({} : NameSet).insert `LeanReachFixture.c),
    (`LeanReachFixture.b, `Tests.Fixture, {}),
    (`LeanReachFixture.c, `Tests.Fixture, {})
  ]
  unless duplicateIndex.size == 3 &&
      (duplicateIndex.upstream `LeanReachFixture.a 10).size == 2 do
    throw <| IO.userError "index did not merge duplicate declarations"
  let longSName := Name.str `LeanReachFixture "ſki"
  let unicodeCandidateIndex := Index.build #[
    (longSName, `Tests.Fixture, {})
  ]
  let unsafeGramRegex ← regex "(?i)ski"
  unless unicodeCandidateIndex.search unsafeGramRegex 10 ==
      unicodeCandidateIndex.searchAll unsafeGramRegex 10 &&
      unicodeCandidateIndex.searchAll unsafeGramRegex 10 == #[longSName] do
    throw <| IO.userError "regex prefilter dropped a Unicode fold equivalent"
  let privateA := mkPrivateNameCore `Tests.PrivateA `LeanReachDuplicate.hidden
  let privateB := mkPrivateNameCore `Tests.PrivateB `LeanReachDuplicate.hidden
  let privateIndex := Index.build #[
    (privateA, `Tests.PrivateA, {}),
    (privateB, `Tests.PrivateB, {})
  ]
  let privateMatches := privateIndex.exactMatches "LeanReachDuplicate.hidden" 10
  unless privateMatches.size == 2 &&
      privateMatches.any (·.moduleName == `Tests.PrivateA) &&
      privateMatches.any (·.moduleName == `Tests.PrivateB) do
    throw <| IO.userError "duplicate private user names were not preserved"
  let roots ← detectRoots
  unless roots.contains `Tests.Fixture do
    throw <| IO.userError "built local modules were not detected"
  unless roots.contains `Mathlib do
    throw <| IO.userError "required Mathlib was not detected"
  let localRoots := roots.filter (· != `Mathlib)
  unless localRoots == localRoots.qsort Name.lt do
    throw <| IO.userError "built local modules were not detected deterministically"
  let mathlibIndex ← unsafe Cache.materializeIndex #[`Mathlib]
  let mathlibTable := SearchCache.Table.ofIndex mathlibIndex
  checkTable mathlibIndex mathlibTable
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
  let fixtureIndex ← unsafe Cache.materializeIndex #[`Tests.Fixture]
  let fixtureTable := SearchCache.Table.ofIndex fixtureIndex
  checkTable fixtureIndex fixtureTable
  let completed := (fixtureTable.modules.foldl
      (init := ({} : NameHashSet)) (·.insert ·))
    |>.erase `Tests.Fixture |>.insert `LeanReach
  let closure := (← unsafe Cache.moduleClosure #[`Tests.Main] completed).map (·.1)
  for expected in #[
      `Tests.Main, `Tests.Integration, `Tests.Session, `Tests.Unit, `Tests.Support,
      `Tests.Fixture, `Tests.PrivateA, `Tests.PrivateB] do
    unless closure.contains expected do
      throw <| IO.userError s!"module closure skipped transitive module '{expected}'"
  let fixtureNames ← unsafe Cache.moduleNames `Tests.Fixture
  let hiddenTheorem :=
    mkPrivateNameCore `Tests.Fixture `LeanReachFixture.hidden_double_zero
  let fixtureEnv ← importEnvironment #[`Tests.Fixture]
  let (planned, _) ← unsafe prettyPrintModuleIO sourcePath fixtureEnv
    `Tests.Fixture fixtureNames fixtureIndex.moduleOf?
  let publicPosition ← expectSome (planned.find? `LeanReachFixture.double)
    "public position fixture is missing"
  let privatePosition ← expectSome (planned.find? hiddenTheorem)
    "private position fixture is missing"
  unless publicPosition.line == 5 && publicPosition.column == 5 &&
      privatePosition.line == 13 && privatePosition.column == 17 do
    throw <| IO.userError "native declaration ranges changed source positions"
  let (monolithic, _) ← unsafe ModuleData.withPrivateOverlay fixtureEnv
      `Tests.Fixture #[] fixtureNames fixtureIndex.moduleOf? fun env =>
    unsafe runCore (env.setMainModule `Tests.Fixture) <| MetaM.run' do
      let source ← unsafe moduleSource sourcePath env `Tests.Fixture fixtureNames
      let bodies := (← prettyPrintPlan fixtureNames).1.foldl
        (init := ({} : NameHashSet)) fun bodies name => bodies.insert name
      return (← prettyPrintModuleWithBodies
        `Tests.Fixture source fixtureNames bodies).1
  unless fixtureNames.all fun name =>
      match planned.find? name, monolithic.find? name with
      | some left, some right => (toJson left).compress == (toJson right).compress
      | _, _ => false do
    throw <| IO.userError "planned PP changed declaration output"
  let cachedWrapped ← expectSome (planned.find? `LeanReachFixture.cachedWrapped)
    "irreducible definition is missing from planned PP"
  unless cachedWrapped.signature.contains "✝" do
    throw <| IO.userError "irreducible definition did not exercise dagger PP"
  let cachedPrivateText ← expectSome (planned.find? `LeanReachFixture.cachedPrivateText)
    "private text fixture is missing from planned PP"
  unless cachedPrivateText.signature.contains "_private." do
    throw <| IO.userError "private text fixture did not exercise cache text"
  unsafe Cache.savePPModule `Tests.Fixture planned
  let roundTripped ← unsafe Cache.loadPPModule `Tests.Fixture
  unless fixtureNames.all roundTripped.contains do
    throw <| IO.userError "PP cache dropped a freshly serialized declaration"
  let selected ← unsafe Cache.loadPP fixtureIndex.moduleOf?
    #[`LeanReachFixture.cachedWrapped]
  let selectedWrapped ← expectSome (selected.find? `LeanReachFixture.cachedWrapped)
    "selective PP cache load dropped an irreducible definition"
  unless (toJson selectedWrapped).compress == (toJson cachedWrapped).compress do
    throw <| IO.userError "selective PP cache load changed declaration output"
  try
    unsafe Cache.savePPModule `Tests.Fixture
      (planned.insert `LeanReachFixture.cachedWrapped {
        cachedWrapped with file := none, line := 0, column := 0
      })
    try
      discard <| unsafe withLookupFor #[`Tests.Fixture]
        "LeanReachFixture.cachedWrapped" (Limits.uniform 0) fun _ _ =>
          (throw <| IO.userError "injected output failure" : IO Unit)
    catch _ => pure ()
    let afterFailure ← unsafe Cache.loadPPModule `Tests.Fixture
    unless afterFailure.contains `LeanReachFixture.double &&
        (afterFailure.find? `LeanReachFixture.cachedWrapped).any (·.hasSource) do
      throw <| IO.userError "incremental PP cache did not repair its source location"
  finally
    unsafe Cache.savePPModule `Tests.Fixture planned
  let mut rejectedMissingSource := false
  try
    discard <| unsafe runCore fixtureEnv <| MetaM.run' <|
      prettyPrintModuleWithBodies `Tests.Fixture (none, {})
        #[`LeanReachFixture.double] {}
  catch _ =>
    rejectedMissingSource := true
  unless rejectedMissingSource do
    throw <| IO.userError "pretty-printer accepted a declaration without source"
  discard <| unsafe QueryCache.build #[`Tests.Fixture]
  for query in #[
      "LeanReachFixture.cachedWrapped",
      "  LeanReachFixture.cachedWrapped  "] do
    unsafe withLookupFor #[`Tests.Fixture]
        query (Limits.uniform 0) fun session result => do
      check session.sourcePath.isEmpty
        "cached query unexpectedly prepared a source environment"
      let .query names := result |
        throw <| IO.userError "exact cached query became a regex search"
      let result ← session.describeQuery names
      check (result.target.signature.contains "✝")
        "cached query lost the serialized irreducible definition"
  let mut rejectedEmpty := false
  try
    discard <| unsafe withLookupFor #[`Tests.Fixture] " "
      (Limits.uniform 0) fun _ _ => pure ()
  catch error =>
    rejectedEmpty := (toString error).contains "declaration query cannot be empty"
  unless rejectedEmpty do
    throw <| IO.userError "empty declaration query was not rejected"
  let rankedCached ← unsafe cachedQuery #[`Tests.Fixture]
    `LeanReachFixture.Topic.ranked
  let expectedQuery := fixtureIndex.queryNamesAt `LeanReachFixture.Topic.ranked
  unless rankedCached.queryNames {} == expectedQuery do
    throw <| IO.userError "cached query does not preserve ranking"
  for limit in #[1, 10, 37, 100] do
    let limits := Limits.uniform limit
    let cached ← unsafe cachedQuery #[`Tests.Fixture]
      `LeanReachFixture.Topic.ranked limits
    unless cached.queryNames limits ==
        fixtureIndex.queryNamesAt `LeanReachFixture.Topic.ranked limits do
      throw <| IO.userError s!"cached query changed limit {limit}"
  let privateRoots := #[`Tests.PrivateA, `Tests.PrivateB]
  discard <| unsafe QueryCache.build privateRoots
  let cachedPrivateMatches ← expectSome
    (← unsafe QueryCache.exactQueries privateRoots "LeanReachDuplicate.hidden" {})
    "cached private exact-name index is missing"
  unless cachedPrivateMatches.size == 2 &&
      cachedPrivateMatches.any (·.target.moduleName == `Tests.PrivateA) &&
      cachedPrivateMatches.any (·.target.moduleName == `Tests.PrivateB) do
    throw <| IO.userError "cached duplicate private names were not preserved"
  let exactPrivate ← unsafe cachedQuery privateRoots privateA
  unless exactPrivate.target.name == privateA do
    throw <| IO.userError "private kernel query key resolved the wrong module"
  let duplicateLeafPattern ← regex "duplicateLeaf"
  let cachedSearch ← expectSome
    (← unsafe QueryCache.search #[`Tests.Fixture] duplicateLeafPattern 10)
    "complete leaf search did not use its shard"
  unless cachedSearch.map (·.name) == fixtureIndex.search duplicateLeafPattern 10 do
    throw <| IO.userError "cached leaf search changed search ordering"
  let substringPattern ← regex "doubleVia"
  let substringSearch ← expectSome
    (← unsafe QueryCache.search #[`Tests.Fixture] substringPattern 10)
    "substring search cache is missing"
  unless substringSearch.map (·.name) == fixtureIndex.search substringPattern 10 do
    throw <| IO.userError "cached substring search changed search ordering"
  let missingPattern ← regex "not_a_declaration_name"
  let missingSearch ← expectSome
    (← unsafe QueryCache.search #[`Tests.Fixture] missingPattern 10)
    "cached empty search fell back to the complete index"
  unless missingSearch.isEmpty do
    throw <| IO.userError "cached empty search returned a declaration"
  let missingExact ← expectSome (← unsafe QueryCache.exactQueries #[`Tests.Fixture]
      "not_a_declaration_name" { search := 2 })
    "exact query cache is unavailable"
  unless missingExact.isEmpty do
    throw <| IO.userError "missing exact query returned a cached declaration"
  for (source, limit) in #[
      (r"double_[zZ]", 1),
      (r"double_(zero|eq)", 10),
      (r"[zZ]", 10),
      (r"LeanReachFixture\.hidden_double_zero", 10),
      (r"^LeanReachFixture\.", 10),
      (r"^.*double.*zero.*$", 10),
      (r"^.*double.?zero.*$", 10),
      (r"^.*(double|cached).*zero.*$", 10),
      ("(?i)^.*DOUBLE.*ZERO.*$", 10),
      ("(?i)DOUBLE_EQ", 10),
      ("(?i)[D]OUBLE_EQ", 10),
      ("(?i)[A-Z]ouble_eq", 10),
      ("definitely_missing_literal", 10)] do
    let pattern ← regex source
    let expected := fixtureIndex.searchAll pattern limit
    unless fixtureIndex.search pattern limit == expected do
      throw <| IO.userError s!"indexed regex prefilter differs for '{source}'"
    let cached ← expectSome
      (← unsafe QueryCache.search #[`Tests.Fixture] pattern limit)
      s!"regex cache is missing for '{source}'"
    unless cached.map (·.name) == expected do
      throw <| IO.userError s!"cached regex differs for '{source}'"
  let layeredRoots := #[`Tests.Fixture, `Mathlib]
  let localCatalog ← unsafe QueryOverlay.buildCatalog layeredRoots `Mathlib
    mathlibTable.modules
  unless localCatalog.baseRoot == `Mathlib &&
      localCatalog.localNames.any (·.name == `LeanReachFixture.double) do
    throw <| IO.userError "lightweight local catalog is missing a declaration"
  unsafe QueryOverlay.saveCatalog layeredRoots localCatalog
  let staleRelations : QueryOverlay.Relations := {
    baseRoot := `Tests.PrivateA, entries := {}, reverse := {}
  }
  let (_, layeredFragments) ← unsafe QueryOverlay.buildRelationsWithFragments
    layeredRoots `Mathlib mathlibTable.modules
  unsafe QueryOverlay.Incremental.saveBaseline layeredRoots
    staleRelations layeredFragments
  let layeredMissing ← expectSome (← unsafe QueryCache.exactQueries layeredRoots
      "definitely_missing_layered_declaration" {})
    "layered exact cache is unavailable"
  let afterMissing ← expectSome
    (← unsafe QueryOverlay.Incremental.loadRelations layeredRoots)
    "stale layered relation sentinel disappeared"
  unless layeredMissing.isEmpty && afterMissing.baseRoot == staleRelations.baseRoot do
    throw <| IO.userError "an exact miss eagerly built layered relations"
  let localPattern ← regex r"^LeanReachFixture\."
  let catalogSearch ← expectSome
    (← unsafe QueryCache.search layeredRoots localPattern 10)
    "local catalog search is unavailable"
  let afterSearch ← expectSome
    (← unsafe QueryOverlay.Incremental.loadRelations layeredRoots)
    "stale layered relation sentinel disappeared"
  unless catalogSearch.map (·.name) == fixtureIndex.searchAll localPattern 10 &&
      afterSearch.baseRoot == staleRelations.baseRoot do
    throw <| IO.userError "local catalog search eagerly built relations"
  let layeredRelations ← unsafe cachedQuery layeredRoots
    `LeanReachFixture.double
  let relations ← expectSome
    (← unsafe QueryOverlay.Incremental.loadRelations layeredRoots)
    "an exact hit did not build layered relations"
  unless relations.baseRoot == localCatalog.baseRoot &&
      relations.entries.size > 0 &&
      relations.affects `LeanReachFixture.double &&
      relations.affects `HAdd.hAdd do
    throw <| IO.userError "local query overlay is missing an affected delta"
  unless !relations.affects `Submodule.span_le do
    throw <| IO.userError "local query overlay marked an unaffected Mathlib query"
  let layeredLocal ← unsafe cachedQuery layeredRoots
    `LeanReachFixture.doubleViaPrivate
  unless layeredLocal.target.name == `LeanReachFixture.doubleViaPrivate do
    throw <| IO.userError "overlay resolved the wrong local declaration"
  unless layeredRelations.downstream.any
      (·.name == `LeanReachFixture.double_eq_add) do
    throw <| IO.userError "local overlay downstream relation is missing"
  let baseHAdd ← unsafe cachedQuery #[`Mathlib] `HAdd.hAdd
  let wideLimits : Limits := { upstream := 37, downstream := 100, search := 2 }
  let wideHAdd ← unsafe cachedQuery #[`Mathlib] `HAdd.hAdd wideLimits
  unless wideHAdd.queryNames wideLimits ==
      mathlibIndex.queryNamesAt `HAdd.hAdd wideLimits do
    throw <| IO.userError "full adjacency cache truncated a wide query"
  let layeredHAdd ← unsafe cachedQuery layeredRoots `HAdd.hAdd
  let expectedHAdd := relations.queryFromBase
    mathlibTable baseHAdd.target (some baseHAdd) {}
  unless layeredHAdd.queryNames {} == expectedHAdd.queryNames {} do
    throw <| IO.userError "lazy overlay query changed affected base relations"
  let layeredBase ← unsafe cachedQuery layeredRoots `Submodule.span_le
  unless layeredBase.target.name == `Submodule.span_le do
    throw <| IO.userError "overlay resolved the wrong base declaration"
  let localizationPattern ← regex "localization_maximal"
  let layeredSearch ← expectSome
    (← unsafe QueryCache.search layeredRoots localizationPattern 10)
    "base substring search did not use the overlay cache"
  unless layeredSearch.map (·.name) ==
      mathlibIndex.search localizationPattern 10 do
    throw <| IO.userError "overlay substring search changed search ordering"
  for limit in #[1, 2, 10] do
    let cached ← expectSome
      (← unsafe QueryCache.search layeredRoots localPattern limit)
      "overlay regex cache is missing"
    unless cached.map (·.name) == fixtureIndex.searchAll localPattern limit do
      throw <| IO.userError "overlay local regex changed global name ordering"
  let crossLayerPattern ←
    regex r"^(LeanReachFixture\.double|Submodule\.span_le)$"
  let crossLayerExpected :=
    #[`LeanReachFixture.double, `Submodule.span_le] |>.qsort Name.lt
  for limit in #[1, 2] do
    let cached ← expectSome
      (← unsafe QueryCache.search layeredRoots crossLayerPattern limit)
      "cross-layer regex cache is missing"
    unless cached.map (·.name) == crossLayerExpected.take limit do
      throw <| IO.userError "cross-layer regex merge changed ordering"
  for (source, limit) in #[
      ("Submodule.span_le", 10),
      ("span_eq", 37),
      ("continuouson_image", 10),
      ("(?i)^.*surject.*padic.*$", 10),
      ("eq", 10)] do
    let pattern ← regex source
    let cached ← expectSome (← unsafe QueryCache.search #[`Mathlib] pattern limit)
      s!"Mathlib search cache is missing for '{source}'"
    unless cached.map (·.name) == mathlibIndex.search pattern limit do
      throw <| IO.userError s!"cached search differs for '{source}'"
  let unicodeClass ← regex "(?i)^WeierstrassCurve\\.[φ]_ne_zero$"
  let unicodeClassExpected := mathlibIndex.searchAll unicodeClass 10
  let unicodeClassCached ← expectSome
    (← unsafe QueryCache.search #[`Mathlib] unicodeClass 10)
    "Mathlib Unicode class search cache is missing"
  unless unicodeClassCached.map (·.name) == unicodeClassExpected &&
      unicodeClassExpected == #[`WeierstrassCurve.Φ_ne_zero] do
    throw <| IO.userError "Unicode class prefilter changed search results"
  let lazyRoots := #[`Tests.Main, `Mathlib]
  let lazyLocal ← unsafe cachedQuery lazyRoots `LeanReachFixture.double
  unless lazyLocal.target.name == `LeanReachFixture.double do
    throw <| IO.userError "recovered overlay resolved the wrong local declaration"
  unless lazyLocal.downstream.any (·.name == `LeanReachFixture.double_eq_add) do
    throw <| IO.userError "recovered overlay lost local reverse dependencies"
end LeanReach.Tests.Integration
