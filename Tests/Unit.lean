import Tests.Support

namespace LeanReach.Tests.Unit

open Lean

unsafe def run : IO Unit := do
  let reported ← IO.mkRef (none : Option Cache.Progress)
  let reporter : Cache.ProgressReporter := fun progress => reported.set (some progress)
  reporter.count .writingQuery 5 10
  let determinate ← expectSome (← reported.get) "cache progress was not reported"
  check (determinate.render ==
      "[5/10] Writing query shards")
    "determinate cache progress changed its counter rendering"
  check (!determinate.finished) "incomplete cache progress was marked finished"
  reporter.count .writingQuery 10 10
  let finished ← expectSome (← reported.get) "finished cache progress was not reported"
  check finished.finished "complete cache progress was not marked finished"
  check (({
      phase := .readingModules
      current := 4
      detail? := some "Mathlib.Algebra"
    } : Cache.Progress).render ==
      "[4/?] Reading modules Mathlib.Algebra")
    "indeterminate cache progress changed its counter rendering"
  IO.FS.withTempDir fun dir => do
    let path := dir / "cache"
    Cache.savePart path "test" (1 : Nat) `LeanReachTests
    let first ← expectSome (← unsafe Cache.loadPart Nat path "test")
      "new cache could not be read"
    check (first == 1) "new cache stored the wrong value"
    Cache.savePart path "test" (2 : Nat) `LeanReachTests
    let value ← expectSome (← unsafe Cache.loadPart Nat path "test")
      "atomically replaced cache could not be read"
    check (value == 2) "cache replacement kept the stale value"
  let values : Array UInt32 := #[0, 1, 127, 128, 16384, 4294967295]
  let encoded := values.foldl Cache.Codec.pushUInt32 ByteArray.empty
  let mut position := 0
  for expected in values do
    let (actual, next) ← expectSome (Cache.Codec.readUInt32 encoded position)
      "varint decoder rejected encoded data"
    check (actual == expected) "varint codec changed a value"
    position := next
  check (position == encoded.size &&
      Cache.Codec.unpackDeltas (Cache.Codec.packDeltas values) == some values)
    "delta codec changed sorted declaration IDs"
  let privateName := mkPrivateNameCore `Tests.Fixture `LeanReachFixture.hidden
  let numericName := Name.num `LeanReachFixture 1099511627776
  let fragment : Cache.ModuleFragment := {
    imports := #[`Init, numericName]
    declarations := #[
      (`LeanReachFixture.double, {
        typeDeps := #[privateName]
        bodyDeps := #[`HAdd.hAdd]
      }),
      (privateName, { typeDeps := #[numericName] })
    ]
  }
  let decodedFragment ← expectSome (Cache.ModuleFragment.decode
      (fragment.encode "fragment-test") "fragment-test")
    "module fragment decoder rejected encoded data"
  let declarationsMatch :=
    decodedFragment.declarations.size == fragment.declarations.size &&
      (decodedFragment.declarations.zip fragment.declarations).all fun
        ((actualName, actualDependencies), (expectedName, expectedDependencies)) =>
          actualName == expectedName && actualDependencies == expectedDependencies
  check (decodedFragment.imports == fragment.imports &&
      declarationsMatch &&
      (Cache.ModuleFragment.decode
        (fragment.encode "fragment-test") "stale-hash").isNone)
    "module fragment codec changed names, edges, or dependency validation"
  let typedIndex := Index.build #[
    (`LeanReachFixture.source, `Tests.Fixture, {
      typeDeps := #[`LeanReachFixture.typeTarget]
      bodyDeps := #[`LeanReachFixture.bodyTarget]
    }),
    (`LeanReachFixture.source, `Tests.Fixture, {
      typeDeps := #[`LeanReachFixture.bodyTarget]
    }),
    (`LeanReachFixture.typeTarget, `Tests.Fixture, {}),
    (`LeanReachFixture.bodyTarget, `Tests.Fixture, {})
  ]
  let sourceId ← expectSome (typedIndex.findId? `LeanReachFixture.source)
    "typed index is missing its source"
  let typeTargetId ← expectSome (typedIndex.findId? `LeanReachFixture.typeTarget)
    "typed index is missing its type target"
  let bodyTargetId ← expectSome (typedIndex.findId? `LeanReachFixture.bodyTarget)
    "typed index is missing its body target"
  let forward := typedIndex.directDependencies sourceId true
  let typeReverse := typedIndex.directDependencies typeTargetId false
  let bodyReverse := typedIndex.directDependencies bodyTargetId false
  check (forward.typeDeps.size == 2 &&
      forward.typeDeps.contains typeTargetId &&
      forward.typeDeps.contains bodyTargetId &&
      forward.bodyDeps.isEmpty &&
      typeReverse.typeDeps == #[sourceId] &&
      bodyReverse.typeDeps == #[sourceId] &&
      bodyReverse.bodyDeps.isEmpty)
    "typed index lost edge kinds or type-dependency precedence"
  let routeIndex := Index.build #[
    (`Route.anchor, `Tests.Fixture, {}),
    (`Route.longA, `Tests.Fixture, { bodyDeps := #[`Route.anchor] }),
    (`Route.longB, `Tests.Fixture, { bodyDeps := #[`Route.longA] }),
    (`Route.short, `Tests.Fixture, { bodyDeps := #[`Route.anchor] }),
    (`Route.target, `Tests.Fixture, {
      bodyDeps := #[`Route.longB, `Route.short]
    })
  ]
  let routeAnchor ← expectSome (routeIndex.findId? `Route.anchor)
    "route index is missing its anchor"
  let routeTarget ← expectSome (routeIndex.findId? `Route.target)
    "route index is missing its target"
  let shortest := routeIndex.shortestRoute routeAnchor routeTarget .consumers 3 20
  let shortestPath ← expectSome shortest.path?
    "bidirectional route search did not find its target"
  check (shortestPath.map (fun (id, _) => (routeIndex.locatedAt! id).name) ==
      #[`Route.anchor, `Route.short, `Route.target] &&
      shortestPath.map (·.2) ==
        #[none, some .bodyDependency, some .bodyDependency])
    "bidirectional route search did not return the shortest typed path"
  let reverseShortest := routeIndex.shortestRoute
    routeTarget routeAnchor .dependencies 3 20
  let reversePath ← expectSome reverseShortest.path?
    "reverse bidirectional route search did not find its target"
  check (reversePath.map (fun (id, _) => (routeIndex.locatedAt! id).name) ==
      #[`Route.target, `Route.short, `Route.anchor])
    "dependency-direction route search reconstructed the wrong path"
  let oldTarget : LocatedName := {
    name := `LeanReachFixture.old, moduleName := `Tests.Fixture
  }
  let keptTarget : LocatedName := {
    name := `LeanReachFixture.kept, moduleName := `Tests.Fixture
  }
  let newTarget : LocatedName := {
    name := `LeanReachFixture.new, moduleName := `Tests.Fixture
  }
  let oldEntry : QueryOverlay.Entry := {
    target := oldTarget
    dependencies := ({} : NameSet).insert `HAdd.hAdd
  }
  let newEntry : QueryOverlay.Entry := {
    target := newTarget
    dependencies := ({} : NameSet).insert `HAdd.hAdd |>.insert `Nat
  }
  let keptEntry : QueryOverlay.Entry := {
    target := keptTarget, dependencies := {}
  }
  let delta : QueryOverlay.Incremental.Delta := {
    removed := #[oldEntry], added := #[newEntry]
  }
  let deltaRelations := delta.applyRelations {
    baseRoot := `Mathlib
    entries := ({} : NameMap QueryOverlay.Entry)
      |>.insert oldTarget.name oldEntry
      |>.insert keptTarget.name keptEntry
    reverse := ({} : NameMap (Array LocatedName)).insert `HAdd.hAdd #[oldTarget]
  }
  let deltaCatalog := deltaRelations.catalog
  check (deltaCatalog.localNames.map (·.name) ==
      #[keptTarget.name, newTarget.name].qsort Name.lt &&
      !deltaRelations.entries.contains oldTarget.name &&
      deltaRelations.entries.contains newTarget.name &&
      (deltaRelations.reverse.find? `HAdd.hAdd).any
        (·.any fun target => target.name == newTarget.name) &&
      (deltaRelations.reverse.find? `Nat).any
        (·.any fun target => target.name == newTarget.name))
    "incremental overlay delta changed catalog or reverse-edge semantics"
  let inverse : QueryOverlay.Incremental.Delta := {
    removed := #[newEntry], added := #[oldEntry]
  }
  let restoredRelations := inverse.applyRelations deltaRelations
  let restoredCatalog := restoredRelations.catalog
  check (restoredCatalog.localNames.map (·.name) ==
      #[oldTarget.name, keptTarget.name].qsort Name.lt &&
      restoredRelations.entries.contains oldTarget.name &&
      !restoredRelations.entries.contains newTarget.name &&
      (restoredRelations.reverse.find? `Nat).isNone)
    "incremental overlay did not compose inverse deltas"
  check (NameSearch.leaf? `Submodule.span_le == some "span_le" &&
      (NameSearch.leaf? (.num `LeanReachGenerated 1)).isNone &&
      (NameSearch.leaf? .anonymous).isNone)
    "name leaf extraction assumed a string component"
  check (NameSearch.trigrams "abcd" == #["abc", "bcd"] &&
      NameSearch.trigrams "αβγδ" == #["αβγ", "βγδ"] &&
      (NameSearch.trigrams "ab").isEmpty)
    "trigram generation changed character-window semantics"
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
  let selected ← expectSome selectedPlan
    "candidate planning discarded a valid posting"
  check (selected == #["abc"])
    "candidate planning retained a duplicate posting"
  let manyAs := "x" ++ String.ofList (List.replicate 17 'a') ++ "y"
  let repetitionNames := #["xaay".toName, "xaaay".toName, manyAs.toName]
  let repetitionIndex := Index.build <| repetitionNames.map fun name =>
    (name, `Tests.Fixture, ({} : Dependencies Name))
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

end LeanReach.Tests.Unit
