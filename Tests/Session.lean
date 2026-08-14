import Tests.Fixture
import Tests.PrivateA
import Tests.PrivateB
import Tests.Support

namespace LeanReach.Tests.SessionTests

open Lean

unsafe def run : IO Unit := do
  let hiddenTheorem :=
    mkPrivateNameCore `Tests.Fixture `LeanReachFixture.hidden_double_zero
  let hiddenDefinition :=
    mkPrivateNameCore `Tests.Fixture `LeanReachFixture.hiddenDouble
  withInteractiveSession #[`Definitely.Missing] fun _ _ => pure ()
  withInteractiveSession #[`Tests.Fixture] fun session runner => do
    let fixtureNames ← unsafe Cache.moduleNames `Tests.Fixture
    let fixtureFragment ← unsafe Cache.moduleFragment `Tests.Fixture
    check (fixtureNames.contains `LeanReachFixture.double)
      "module fragment is missing a source declaration"
    check (!fixtureNames.any (·.toString.contains "noConfusion"))
      "module fragment contains a generated declaration"
    check (fixtureNames.contains hiddenTheorem && fixtureNames.contains hiddenDefinition)
      "module fragment is missing a private declaration"
    let doubleDependencies ← expectSome
      (fixtureFragment.declarations.find? (·.1 == `LeanReachFixture.double) |>.map (·.2))
      "module fragment is missing double dependencies"
    check (doubleDependencies.typeDeps.contains `Nat &&
        doubleDependencies.bodyDeps.contains `HAdd.hAdd &&
        !doubleDependencies.bodyDeps.contains `Nat)
      "module fragment did not separate type and body dependencies"
    let theoremDependencies ← expectSome
      (fixtureFragment.declarations.find?
        (·.1 == `LeanReachFixture.double_zero_again) |>.map (·.2))
      "module fragment is missing theorem dependencies"
    check (theoremDependencies.typeDeps.contains `LeanReachFixture.double &&
        theoremDependencies.bodyDeps.contains `LeanReachFixture.double_zero)
      "theorem fragment did not separate statement and proof dependencies"
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
      let first ← expectSome result.upstream[0]? "ranked dependencies are empty"
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

  withInteractiveSession #[`Tests.PrivateA, `Tests.PrivateB] fun session runner =>
    runner "LeanReachDuplicate.hidden" {} fun
      | .search names => do
        let declarations ← session.describeNames names
        check (declarations.size == 2)
          "duplicate private user names did not return both matches"
        check (declarations.all fun item => item.file.isSome && item.line > 0)
          "duplicate private match is missing its source path or line"
      | .query _ =>
        throw <| IO.userError "duplicate private user name became a dependency query"

end LeanReach.Tests.SessionTests
