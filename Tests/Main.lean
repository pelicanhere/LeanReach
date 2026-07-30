import LeanReach
import Tests.Fixture
import Tests.PrivateA
import Tests.PrivateB

namespace LeanReach.Tests

open Lean Meta

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def regex (source : String) : IO SearchPattern :=
  IO.ofExcept <| SearchPattern.compileRegex source |>.mapError IO.userError

private def tokens (values : Array String) : IO SearchPattern :=
  IO.ofExcept <| SearchPattern.compileTokens values |>.mapError IO.userError

private unsafe def runTests : IO Unit := do
  unless NameSearch.trigrams "abcd" == #["abc", "bcd"] &&
      NameSearch.trigrams "αβγδ" == #["αβγ", "βγδ"] &&
      (NameSearch.trigrams "ab").isEmpty do
    throw <| IO.userError "trigram generation changed character-window semantics"
  let spanPattern ← regex "span_(le|eq_bot)"
  check (spanPattern.isMatch `Submodule.span_le)
    "unanchored regex did not match a declaration name"
  check (!(← regex "^span").isMatch `Submodule.span_le)
    "regex anchor was ignored"
  check ((← regex "(?i)SPAN_LE").isMatch `Submodule.span_le)
    "case-insensitive regex did not match"
  let acceleratedCaseFold ← regex "(?i)DOUBLE_EQ"
  let .postings _ := acceleratedCaseFold.candidatePlan |
    throw <| IO.userError "safe case-insensitive regex did not use postings"
  check ((← regex "(?i)^LeanReachFixture\\.[D]ouble$").isMatch
      `LeanReachFixture.double)
    "case-insensitive regex did not fold an explicit character class"
  check ((← regex "(?i)^LeanReachFixture\\.[A-Z]ouble$").isMatch
      `LeanReachFixture.double)
    "case-insensitive regex did not fold a character range"
  check (!(← regex "(?i)^LeanReachFixture\\.[^D]ouble$").isMatch
      `LeanReachFixture.double)
    "case-insensitive regex changed a negated character class"
  check ((← regex "(?i)^LeanReachFixture\\.[^D]ouble$").isMatch
      `LeanReachFixture.xouble)
    "case-insensitive regex rejected a valid negated character class"
  check ((← regex "(?i)^WeierstrassCurve\\.[φ]_ne_zero$").isMatch
      `WeierstrassCurve.Φ_ne_zero)
    "case-insensitive regex did not fold a Unicode character class"
  check ((← regex r"Submodule\.span_le").isMatch `Submodule.span_le)
    "escaped regex punctuation did not match literally"
  check ((← tokens #["LE", "submodule", "le"]).isMatch `Submodule.span_le)
    "unordered token search did not normalize or deduplicate tokens"
  check ((← tokens #["φ_NE_ZERO"]).isMatch `WeierstrassCurve.Φ_ne_zero)
    "unordered token search did not apply Unicode simple case folding"
  check (SearchPattern.compileRegex "(" |>.toOption |>.isNone)
    "invalid regex was accepted"
  check (SearchPattern.compileRegex "a{1025}" |>.toOption |>.isNone)
    "oversized regex repetition was accepted"
  let oversizedClass :=
    "[" ++ String.ofList (List.replicate 3000 'a') ++ "]"
  check (SearchPattern.compileRegex oversizedClass |>.toOption |>.isNone)
    "oversized regex character class was accepted"
  let deeplyNestedClass :=
    (List.replicate 130 "[^").foldl (· ++ ·) "" ++ "a" ++
      String.ofList (List.replicate 130 ']')
  check (SearchPattern.compileRegex deeplyNestedClass |>.toOption |>.isNone)
    "deeply nested regex character class was accepted"
  check (SearchPattern.unionIds #[] #[1, 2] == #[1, 2] &&
      SearchPattern.unionIds #[1, 2] #[] == #[1, 2] &&
      SearchPattern.unionIds #[1, 2, 4] #[2, 3, 4] == #[1, 2, 3, 4])
    "sorted posting union changed ordering or deduplication"
  let selectedPlan := SearchPattern.CandidatePlan.postings #[
    #["abc"], #["abc", "def"]
  ] |>.select fun gram => if gram == "abc" then some 1 else some 2
  let .postings selected := selectedPlan |
    throw <| IO.userError "candidate planning discarded a valid posting"
  check (selected == #[#["abc"]])
    "candidate planning retained a duplicate posting"
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
  let longSName := Name.str `LeanReachFixture "ſki"
  let unicodeCandidateIndex := Index.build #[
    (longSName, `Tests.Fixture, {})
  ]
  let unsafeGramTokens ← tokens #["ski"]
  unless unicodeCandidateIndex.search unsafeGramTokens 10 ==
      unicodeCandidateIndex.searchAll unsafeGramTokens 10 &&
      unicodeCandidateIndex.searchAll unsafeGramTokens 10 == #[longSName] do
    throw <| IO.userError "token prefilter dropped a Unicode fold equivalent"
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
  let some publicPosition := planned.find? `LeanReachFixture.double |
    throw <| IO.userError "public position fixture is missing"
  let some privatePosition := planned.find? hiddenTheorem |
    throw <| IO.userError "private position fixture is missing"
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
  try
    unsafe Cache.savePPModule `Tests.Fixture
      (planned.erase `LeanReachFixture.cachedWrapped)
    try
      discard <| unsafe withCachedQueryFor #[`Tests.Fixture]
        "LeanReachFixture.cachedWrapped" (Limits.uniform 0) fun _ _ =>
          (throw <| IO.userError "injected output failure" : IO Unit)
    catch _ => pure ()
    unless (← unsafe Cache.loadPPModule `Tests.Fixture).contains
        `LeanReachFixture.cachedWrapped do
      throw <| IO.userError "PP result was not cached before output failure"
  finally
    unsafe Cache.savePPModule `Tests.Fixture planned
  let (withoutSource, _) ← unsafe runCore fixtureEnv <| MetaM.run' <|
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
  let .ok (some mathlibSubstring) ← unsafe QueryCache.resolve #[`Mathlib]
      "isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maxima" |
    throw <| IO.userError "Mathlib substring query did not use its search cache"
  unless mathlibSubstring.target.name ==
      `isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal do
    throw <| IO.userError "Mathlib substring query resolved the wrong declaration"
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
  let duplicateLeafPattern ← regex "duplicateLeaf"
  let some cachedSearch ← unsafe QueryCache.search #[`Tests.Fixture]
      duplicateLeafPattern 10 |
    throw <| IO.userError "complete leaf search did not use its shard"
  unless cachedSearch.map (·.name) == fixtureIndex.search duplicateLeafPattern 10 do
    throw <| IO.userError "cached leaf search changed search ordering"
  let substringPattern ← regex "doubleVia"
  let some substringSearch ← unsafe QueryCache.search #[`Tests.Fixture]
      substringPattern 10 |
    throw <| IO.userError "substring search cache is missing"
  unless substringSearch.map (·.name) == fixtureIndex.search substringPattern 10 do
    throw <| IO.userError "cached substring search changed search ordering"
  let missingPattern ← regex "not_a_declaration_name"
  let some missingSearch ← unsafe QueryCache.search #[`Tests.Fixture]
      missingPattern 10 |
    throw <| IO.userError "cached empty search fell back to the complete index"
  unless missingSearch.isEmpty do
    throw <| IO.userError "cached empty search returned a declaration"
  for (source, limit) in #[
      (r"double_[zZ]", 1),
      (r"double_(zero|eq)", 10),
      (r"[zZ]", 10),
      (r"LeanReachFixture\.hidden_double_zero", 10),
      (r"^LeanReachFixture\.", 10),
      ("(?i)DOUBLE_EQ", 10),
      ("(?i)[D]OUBLE_EQ", 10),
      ("(?i)[A-Z]ouble_eq", 10),
      ("definitely_missing_literal", 10)] do
    let pattern ← regex source
    let expected := fixtureIndex.searchAll pattern limit
    unless fixtureIndex.search pattern limit == expected do
      throw <| IO.userError s!"indexed regex prefilter differs for '{source}'"
    let some cached ← unsafe QueryCache.search #[`Tests.Fixture] pattern limit |
      throw <| IO.userError s!"regex cache is missing for '{source}'"
    unless cached.map (·.name) == expected do
      throw <| IO.userError s!"cached regex differs for '{source}'"
  for (values, limit) in #[
      (#["double_", "z"], 1),
      (#["zero", "double"], 10),
      (#["z"], 10),
      (#["DOUBLE", "ZERO", "double"], 10)] do
    let pattern ← tokens values
    let expected := fixtureIndex.searchAll pattern limit
    unless fixtureIndex.search pattern limit == expected do
      throw <| IO.userError s!"indexed token prefilter differs for '{values}'"
    let some cached ← unsafe QueryCache.search #[`Tests.Fixture] pattern limit |
      throw <| IO.userError s!"token cache is missing for '{values}'"
    unless cached.map (·.name) == expected do
      throw <| IO.userError s!"cached token search differs for '{values}'"
  let layeredRoots := #[`Tests.Fixture, `Mathlib]
  discard <| unsafe QueryCache.build layeredRoots
  let some overlay ← unsafe QueryOverlay.load layeredRoots |
    throw <| IO.userError "local query overlay is missing"
  unless overlay.baseRoot == `Mathlib && overlay.entries.size > 0 do
    throw <| IO.userError "local query overlay has the wrong base or no declarations"
  unless (overlay.cached? `LeanReachFixture.double).isSome &&
      (overlay.cached? `HAdd.hAdd).isSome do
    throw <| IO.userError "local query overlay is missing an affected delta"
  unless (overlay.cached? `Submodule.span_le).isNone do
    throw <| IO.userError "local query overlay copied an unaffected Mathlib query"
  let .ok (some layeredLocal) ← unsafe QueryCache.resolve layeredRoots
      "doubleViaPrivate" |
    throw <| IO.userError "local declaration did not resolve through the overlay"
  unless layeredLocal.target.name == `LeanReachFixture.doubleViaPrivate do
    throw <| IO.userError "overlay resolved the wrong local declaration"
  let .ok (some layeredSubstring) ← unsafe QueryCache.resolve layeredRoots
      "cachedWrap" |
    throw <| IO.userError "local substring did not resolve through the overlay"
  unless layeredSubstring.target.name == `LeanReachFixture.cachedWrapped do
    throw <| IO.userError "overlay substring resolved the wrong local declaration"
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
  let localizationPattern ← regex "localization_maximal"
  let some layeredSearch ← unsafe QueryCache.search layeredRoots
      localizationPattern 10 |
    throw <| IO.userError "base substring search did not use the overlay cache"
  unless layeredSearch.map (·.name) ==
      mathlibIndex.search localizationPattern 10 do
    throw <| IO.userError "overlay substring search changed search ordering"
  let localPattern ← regex r"^LeanReachFixture\."
  for limit in #[1, 2, 10] do
    let some cached ← unsafe QueryCache.search layeredRoots localPattern limit |
      throw <| IO.userError "overlay regex cache is missing"
    unless cached.map (·.name) == fixtureIndex.searchAll localPattern limit do
      throw <| IO.userError "overlay local regex changed global name ordering"
  let crossLayerPattern ←
    regex r"^(LeanReachFixture\.double|Submodule\.span_le)$"
  let crossLayerExpected :=
    #[`LeanReachFixture.double, `Submodule.span_le] |>.qsort Name.lt
  for limit in #[1, 2] do
    let some cached ← unsafe QueryCache.search layeredRoots crossLayerPattern limit |
      throw <| IO.userError "cross-layer regex cache is missing"
    unless cached.map (·.name) == crossLayerExpected.take limit do
      throw <| IO.userError "cross-layer regex merge changed ordering"
  for (source, limit) in #[
      ("Submodule.span_le", 10),
      ("span_eq", 37),
      ("continuouson_image", 10),
      ("eq", 10)] do
    let pattern ← regex source
    let some cached ← unsafe QueryCache.search #[`Mathlib] pattern limit |
      throw <| IO.userError s!"Mathlib search cache is missing for '{source}'"
    unless cached.map (·.name) == mathlibIndex.search pattern limit do
      throw <| IO.userError s!"cached search differs for '{source}'"
  let unicodeTokens ← tokens #["WEIERSTRASSCURVE.φ_NE_ZERO"]
  let unicodeExpected := mathlibIndex.searchAll unicodeTokens 10
  let some unicodeCached ← unsafe QueryCache.search #[`Mathlib]
      unicodeTokens 10 |
    throw <| IO.userError "Mathlib Unicode token search cache is missing"
  unless unicodeCached.map (·.name) == unicodeExpected &&
      unicodeExpected == #[`WeierstrassCurve.Φ_ne_zero] do
    throw <| IO.userError "Unicode token prefilter changed search results"
  let unicodeClass ← regex "(?i)^WeierstrassCurve\\.[φ]_ne_zero$"
  let unicodeClassExpected := mathlibIndex.searchAll unicodeClass 10
  let some unicodeClassCached ← unsafe QueryCache.search #[`Mathlib]
      unicodeClass 10 |
    throw <| IO.userError "Mathlib Unicode class search cache is missing"
  unless unicodeClassCached.map (·.name) == unicodeClassExpected &&
      unicodeClassExpected == #[`WeierstrassCurve.Φ_ne_zero] do
    throw <| IO.userError "Unicode class prefilter changed search results"
  let lazyRoots := #[`Tests.Main, `Mathlib]
  let .ok (some lazyLocal) ← unsafe QueryCache.resolve lazyRoots
      "LeanReachFixture.double" |
    throw <| IO.userError "query did not include an imported local module"
  unless lazyLocal.target.name == `LeanReachFixture.double do
    throw <| IO.userError "recovered overlay resolved the wrong local declaration"
  unless lazyLocal.downstream.any (·.name == `LeanReachFixture.double_eq_add) do
    throw <| IO.userError "recovered overlay lost local reverse dependencies"
  withInteractiveSession #[`Definitely.Missing] fun _ _ => pure ()
  withInteractiveSession #[`Tests.Fixture] fun session runner => do
    let fixtureNames ← unsafe Cache.moduleNames `Tests.Fixture
    unless fixtureNames.contains `LeanReachFixture.double do
      throw <| IO.userError "module fragment is missing a source declaration"
    unless !fixtureNames.any (·.toString.contains "noConfusion") do
      throw <| IO.userError "module fragment contains a generated declaration"
    unless fixtureNames.contains hiddenTheorem && fixtureNames.contains hiddenDefinition do
      throw <| IO.userError "module fragment is missing a private declaration"
    let query (name : String) (limits : Limits)
        (action : QueryResult → IO Unit) : IO Unit :=
      runner.query name limits fun names => do
        action (← session.describeQuery names)
    let search (pattern : String) (action : Array Declaration → IO Unit) : IO Unit := do
      runner.search (← regex pattern) 10 fun names => do
        action (← session.describeNames names)

    query "LeanReachFixture.double" (Limits.uniform 100) fun result => do
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

    query "LeanReachFixture.doubleViaPrivate" {} fun result => do
      check (result.target.signature.contains "hiddenDouble")
        "definition body through a private constant was not pretty-printed"

    query "LeanReachFixture.hiddenDouble" {} fun result => do
      check (result.target.name == hiddenDefinition.toString)
        "private definition lost its stable query name"
      check (result.target.line == 17)
        "private definition has the wrong source line"
      check (result.target.signature.contains ":=\n")
        "private definition body is missing"
      check (!result.target.signature.contains "_private" &&
          !result.target.signature.contains "✝")
        s!"private definition signature was not printed as a user name:\n\
          {result.target.signature}"
      check
        (result.downstream.any fun declaration =>
          declaration.name == "LeanReachFixture.doubleViaPrivate")
        "private definition downstream relation is missing"

    query "LeanReachFixture.hidden_double_zero" (Limits.uniform 100) fun result => do
      check (result.target.name == hiddenTheorem.toString)
        "private theorem lost its stable query name"
      check (result.target.line == 13)
        "private theorem has the wrong source line"
      check (!result.target.signature.contains ":=\n")
        "private theorem proof body was printed"
      check
        (result.upstream.any fun declaration =>
          declaration.name == "LeanReachFixture.double_zero")
        "private theorem proof dependency is missing"
      check
        (result.downstream.any fun declaration =>
          declaration.name == "LeanReachFixture.double_zero_via_private")
        "private theorem downstream relation is missing"

    query "LeanReachFixture.double_eq_add" (Limits.uniform 100) fun result => do
      check (result.target.signature.contains "n + n")
        "theorem signature was not pretty-printed with notation"
      check
        (result.upstream.any fun declaration =>
          declaration.name == "LeanReachFixture.double")
        "upstream relation is missing"

    query "LeanReachFixture.double_zero_again" (Limits.uniform 100) fun result => do
      check
        (result.upstream.any fun declaration =>
          declaration.name == "LeanReachFixture.double_zero")
        "proof-only upstream relation is missing"

    query "LeanReachFixture.double_zero" (Limits.uniform 100) fun result => do
      check
        (result.downstream.any fun declaration =>
          declaration.name == "LeanReachFixture.double_zero_again")
        "proof-only downstream relation is missing"
      check
        (result.downstream.any fun declaration =>
          declaration.name == hiddenTheorem.toString)
        "private proof helper dependency is missing"

    query "LeanReachFixture.Topic.ranked" (Limits.uniform 1) fun result => do
      check (result.upstream.size == 1)
        "dependency limit was not applied during ranking"
      let some first := result.upstream[0]? |
        throw <| IO.userError "ranked dependencies are empty"
      check (first.name == "LeanReachFixture.Topic.nearby")
        "nearby dependency was not ranked first"

    query "Add" {} fun result => do
      check (result.target.signature.contains "fields:")
        "class fields are missing"
      check (result.target.signature.contains "Add.add")
        "class field signature is missing"

    search "double_eq" fun result => do
      check
        (result.any fun item =>
          item.name == "LeanReachFixture.double_eq_add")
        "local name search is missing"
    search "hidden_double" fun result => do
      check (result.any fun item => item.name == hiddenTheorem.toString)
        "private name search is missing"
    search "LeanReachFixture.Color.noConfusion" fun result => do
      check result.isEmpty "generated declaration was not blacklisted"
    search "LeanReachFixture.Box.value" fun result => do
      check (result.any fun item => item.name == "LeanReachFixture.Box.value")
        "structure projection was blacklisted"
    search "double_zero_again" fun result => do
      check (!result.isEmpty) "interactive session search is missing"

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
