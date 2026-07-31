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

private unsafe def cachedQuery (roots : Array Name) (name : Name)
    (limits : Limits := {}) : IO CachedQuery := do
  let results ← QueryCache.exactQueries roots name.toString
    { limits with search := 2 }
  let some results := results |
    throw <| IO.userError s!"query cache is unavailable for '{name}'"
  let some query := results.find? (·.target.name == name) |
    throw <| IO.userError s!"query cache is missing '{name}'"
  return query

private def checkTable (index : Index) (table : SearchCache.Table) : IO Unit := do
  let entries := index.catalog.1
  let (reverseCounts, forwardCounts) := index.relationCountsById
  check (table.isValid && table.names == entries.map (·.name) &&
      table.reverseCounts == reverseCounts &&
      table.forwardCounts == forwardCounts)
    "declaration table changed index dimensions"
  for (expected, id) in entries.zipIdx do
    let actual := table.locatedAt! id.toUInt32
    check (actual.name == expected.name && actual.moduleName == expected.moduleName)
      s!"declaration table changed '{expected.name}'"

private unsafe def runTests : IO Unit := do
  IO.FS.withTempDir fun dir => do
    let path := dir / "cache"
    Cache.savePart path "test" (1 : Nat) `LeanReachTests
    let some first ← unsafe Cache.loadPart Nat path "test" |
      throw <| IO.userError "new cache could not be read"
    check (first == 1) "new cache stored the wrong value"
    Cache.savePart path "test" (2 : Nat) `LeanReachTests
    let some value ← unsafe Cache.loadPart Nat path "test" |
      throw <| IO.userError "atomically replaced cache could not be read"
    check (value == 2) "cache replacement kept the stale value"
  let values : Array UInt32 := #[0, 1, 127, 128, 16384, 4294967295]
  let encoded := values.foldl Cache.Codec.pushUInt32 ByteArray.empty
  let mut position := 0
  for expected in values do
    let some (actual, next) := Cache.Codec.readUInt32 encoded position |
      throw <| IO.userError "varint decoder rejected encoded data"
    check (actual == expected) "varint codec changed a value"
    position := next
  check (position == encoded.size &&
      Cache.Codec.unpackDeltas (Cache.Codec.packDeltas values) == some values)
    "delta codec changed sorted declaration IDs"
  check (NameSearch.leaf? `Submodule.span_le == some "span_le" &&
      (NameSearch.leaf? (.num `LeanReachGenerated 1)).isNone &&
      (NameSearch.leaf? .anonymous).isNone)
    "name leaf extraction assumed a string component"
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
  let naturalRegex ← regex "(?i)^.*padic.*surject.*$"
  let .postings _ := naturalRegex.candidatePlan |
    throw <| IO.userError "anchored wildcard regex did not use literal postings"
  let shortAlternative ← regex "^.*(double|x).*$"
  let .all := shortAlternative.candidatePlan |
    throw <| IO.userError "regex branch without a trigram was unsafely prefiltered"
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
  check (SearchPattern.mergeSortedIds #[] #[1, 2] == #[1, 2] &&
      SearchPattern.mergeSortedIds #[1, 2] #[] == #[1, 2] &&
      SearchPattern.mergeSortedIds #[1, 2, 4] #[2, 3, 4] == #[1, 2, 3, 4])
    "sorted posting union changed ordering or deduplication"
  let selectedPlan := SearchPattern.CandidatePlan.postings #[
    #["abc"], #["abc", "def"]
  ] |>.select fun gram => if gram == "abc" then some 1 else some 2
  let .postings selected := selectedPlan |
    throw <| IO.userError "candidate planning discarded a valid posting"
  check (selected == #[#["abc"]])
    "candidate planning retained a duplicate posting"
  let manyAs := "x" ++ String.ofList (List.replicate 17 'a') ++ "y"
  let repetitionNames := #["xaay".toName, "xaaay".toName, manyAs.toName]
  let repetitionIndex := Index.build <| repetitionNames.map fun name =>
    (name, `Tests.Fixture, ({} : NameSet))
  for (source, expected) in #[
      ("^xa+y$", "xaay".toName),
      ("^xa{2,3}y$", "xaay".toName),
      ("^x(a|b){2}y$", "xaay".toName),
      ("^xa{17}y$", manyAs.toName)] do
    let pattern ← regex source
    check (pattern.isMatch expected)
      s!"repetition regex '{source}' did not match its fixture"
    check (repetitionIndex.search pattern 10 == repetitionIndex.searchAll pattern 10)
      s!"repetition candidate plan dropped a match for '{source}'"
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
  for expected in #[`Tests.Main, `Tests.Fixture, `Tests.PrivateA, `Tests.PrivateB] do
    unless closure.contains expected do
      throw <| IO.userError s!"module closure skipped transitive module '{expected}'"
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
  let some cachedPrivateMatches ← unsafe QueryCache.exactQueries privateRoots
      "LeanReachDuplicate.hidden" {} |
    throw <| IO.userError "cached private exact-name index is missing"
  unless cachedPrivateMatches.size == 2 &&
      cachedPrivateMatches.any (·.target.moduleName == `Tests.PrivateA) &&
      cachedPrivateMatches.any (·.target.moduleName == `Tests.PrivateB) do
    throw <| IO.userError "cached duplicate private names were not preserved"
  let exactPrivate ← unsafe cachedQuery privateRoots privateA
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
  let some missingExact ← unsafe QueryCache.exactQueries #[`Tests.Fixture]
      "not_a_declaration_name" { search := 2 } |
    throw <| IO.userError "exact query cache is unavailable"
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
    let some cached ← unsafe QueryCache.search #[`Tests.Fixture] pattern limit |
      throw <| IO.userError s!"regex cache is missing for '{source}'"
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
  unsafe QueryOverlay.saveRelations layeredRoots staleRelations
  let some layeredMissing ← unsafe QueryCache.exactQueries layeredRoots
      "definitely_missing_layered_declaration" {} |
    throw <| IO.userError "layered exact cache is unavailable"
  let some afterMissing ← unsafe QueryOverlay.loadRelations layeredRoots |
    throw <| IO.userError "stale layered relation sentinel disappeared"
  unless layeredMissing.isEmpty && afterMissing.baseRoot == staleRelations.baseRoot do
    throw <| IO.userError "an exact miss eagerly built layered relations"
  let localPattern ← regex r"^LeanReachFixture\."
  let some catalogSearch ← unsafe QueryCache.search layeredRoots localPattern 10 |
    throw <| IO.userError "local catalog search is unavailable"
  let some afterSearch ← unsafe QueryOverlay.loadRelations layeredRoots |
    throw <| IO.userError "stale layered relation sentinel disappeared"
  unless catalogSearch.map (·.name) == fixtureIndex.searchAll localPattern 10 &&
      afterSearch.baseRoot == staleRelations.baseRoot do
    throw <| IO.userError "local catalog search eagerly built relations"
  let layeredRelations ← unsafe cachedQuery layeredRoots
    `LeanReachFixture.double
  let some relations ← unsafe QueryOverlay.loadRelations layeredRoots |
    throw <| IO.userError "an exact hit did not build layered relations"
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
  let some layeredSearch ← unsafe QueryCache.search layeredRoots
      localizationPattern 10 |
    throw <| IO.userError "base substring search did not use the overlay cache"
  unless layeredSearch.map (·.name) ==
      mathlibIndex.search localizationPattern 10 do
    throw <| IO.userError "overlay substring search changed search ordering"
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
      ("(?i)^.*surject.*padic.*$", 10),
      ("eq", 10)] do
    let pattern ← regex source
    let some cached ← unsafe QueryCache.search #[`Mathlib] pattern limit |
      throw <| IO.userError s!"Mathlib search cache is missing for '{source}'"
    unless cached.map (·.name) == mathlibIndex.search pattern limit do
      throw <| IO.userError s!"cached search differs for '{source}'"
  let unicodeClass ← regex "(?i)^WeierstrassCurve\\.[φ]_ne_zero$"
  let unicodeClassExpected := mathlibIndex.searchAll unicodeClass 10
  let some unicodeClassCached ← unsafe QueryCache.search #[`Mathlib]
      unicodeClass 10 |
    throw <| IO.userError "Mathlib Unicode class search cache is missing"
  unless unicodeClassCached.map (·.name) == unicodeClassExpected &&
      unicodeClassExpected == #[`WeierstrassCurve.Φ_ne_zero] do
    throw <| IO.userError "Unicode class prefilter changed search results"
  let lazyRoots := #[`Tests.Main, `Mathlib]
  let lazyLocal ← unsafe cachedQuery lazyRoots `LeanReachFixture.double
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
      runner name limits fun
        | .query names => do
          let result ← session.describeQuery names
          check (result.all.all (·.hasSource))
            s!"dependency query '{name}' returned a declaration without source"
          action result
        | .search _ =>
          throw <| IO.userError s!"exact declaration '{name}' became a regex search"
    let search (pattern : String) (action : Array Declaration → IO Unit) : IO Unit := do
      runner pattern {} fun
        | .search names => do
          let result ← session.describeNames names
          check (result.all (·.hasSource))
            s!"regex '{pattern}' returned a declaration without source"
          action result
        | .query _ =>
          throw <| IO.userError s!"regex pattern '{pattern}' became an exact query"

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
      check (result.all fun item => item.file.isSome && item.line > 0)
        "regex result is missing its source path or line"
    search "hidden_double" fun result => do
      check (result.any fun item => item.name == hiddenTheorem.toString)
        "private name search is missing"
    search "LeanReachFixture.Color.noConfusion" fun result => do
      check result.isEmpty "generated declaration was not blacklisted"
    search r"^LeanReachFixture\.Box\.value$" fun result => do
      check (result.any fun item => item.name == "LeanReachFixture.Box.value")
        "structure projection was blacklisted"
    search "double_zero_again" fun result => do
      check (!result.isEmpty) "interactive session search is missing"

  withInteractiveSession privateRoots fun session runner =>
    runner "LeanReachDuplicate.hidden" {} fun
      | .search names => do
        let declarations ← session.describeNames names
        check (declarations.size == 2)
          "duplicate private user names did not return both matches"
        check (declarations.all fun item => item.file.isSome && item.line > 0)
          "duplicate private match is missing its source path or line"
      | .query _ =>
        throw <| IO.userError "duplicate private user name became a dependency query"

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
