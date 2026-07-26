import Lean.CoreM
import Lean.Data.Json
import Lean.Data.Name
import Lean.DeclarationRange
import Lean.OriginalConstKind
import Lean.Server.References
import Lean.Util.FoldConsts
import Lean.Util.Path

namespace LeanReach

open Lean Lean.Core

/-- Which side of a declaration's dependency neighborhood to inspect. -/
inductive Direction where
  | both
  | upstream
  | downstream
  deriving Repr, BEq

namespace Direction

def includesUpstream : Direction → Bool
  | .both | .upstream => true
  | .downstream => false

def includesDownstream : Direction → Bool
  | .both | .downstream => true
  | .upstream => false

end Direction

/--
Dependency semantics. Source mode follows resolved source references in `.ilean` files; kernel mode
follows constants that occur in elaborated types and values.
-/
inductive DependencyMode where
  | source
  | kernel
  deriving Repr, BEq

namespace DependencyMode

def label : DependencyMode → String
  | .source => "source"
  | .kernel => "kernel"

end DependencyMode

/-- Options that affect a dependency query after the requested modules are loaded. -/
structure QueryConfig where
  query : String
  mode : DependencyMode := .source
  direction : Direction := .both
  depth : Nat := 1
  limit : Nat := 20
  includeInternal : Bool := false
  deriving Repr

/-- A source location. Lines and columns are both one-based for CLI consumers. -/
structure SourceLocation where
  moduleName : Option String
  file : Option String
  line : Option Nat
  column : Option Nat
  endLine : Option Nat
  endColumn : Option Nat
  deriving Repr, ToJson

/-- The agent-facing description of a declaration. -/
structure DeclarationView where
  name : String
  kind : String
  source : SourceLocation
  deriving Repr, ToJson

/-- A declaration related to the target, together with one lightweight path witness. -/
structure RelationView where
  distance : Nat
  via : Option String
  declaration : DeclarationView
  deriving Repr, ToJson

/-- A bounded list of results plus the number found before applying the output limit. -/
structure RelationList where
  total : Nat
  items : Array RelationView
  deriving Repr, ToJson

/-- Stable JSON payload for a declaration-neighborhood query. -/
structure QueryResult where
  schemaVersion : Nat := 1
  query : String
  mode : String
  target : DeclarationView
  upstream : RelationList
  downstream : RelationList
  deriving Repr, ToJson

/-- A failed exact/suffix resolution with ranked declarations that may have been intended. -/
structure QueryFailure where
  schemaVersion : Nat := 1
  error : String
  candidates : Array DeclarationView
  deriving Repr, ToJson

/-- Stable JSON payload for name search. -/
structure SearchResult where
  schemaVersion : Nat := 1
  query : String
  total : Nat
  items : Array DeclarationView
  deriving Repr, ToJson

private structure RawRelation where
  name : Name
  distance : Nat
  via : Option Name

private structure ResolveFailure where
  message : String
  candidates : Array Name

private def constantKind : ConstantKind → String
  | .axiom => "axiom"
  | .defn => "definition"
  | .thm => "theorem"
  | .opaque => "opaque"
  | .quot => "quotient"
  | .induct => "inductive"
  | .ctor => "constructor"
  | .recursor => "recursor"

private def visibleName (includeInternal : Bool) (name : Name) : Bool :=
  includeInternal || !name.isInternalDetail

private def nameString (name : Name) : String :=
  name.toString (escape := false)

private def nameScore (query : String) (name : Name) : Option Nat :=
  let candidate := nameString name
  let queryLower := query.toLower
  let candidateLower := candidate.toLower
  if candidate == query then
    some 0
  else if candidate.endsWith ("." ++ query) then
    some 1
  else if candidateLower == queryLower then
    some 2
  else if candidateLower.endsWith ("." ++ queryLower) then
    some 3
  else if candidateLower.contains queryLower then
    some 4
  else
    none

private def scoredNames (env : Environment) (query : String) (includeInternal : Bool) :
    Array (Nat × Name) := Id.run do
  let mut hits := #[]
  for (name, _) in env.constants do
    if visibleName includeInternal name then
      if let some score := nameScore query name then
        hits := hits.push (score, name)
  return hits.qsort fun left right =>
    left.1 < right.1 || (left.1 == right.1 && Name.quickLt left.2 right.2)

private def resolveName (env : Environment) (query : String) (includeInternal : Bool) :
    Except ResolveFailure Name := do
  let exact := query.toName
  if env.contains exact && visibleName includeInternal exact then
    return exact
  let hits := scoredNames env query includeInternal
  let suggestions := (hits.take 10).map (·.2)
  let some best := hits[0]? | throw {
    message := s!"unknown declaration '{query}'"
    candidates := #[]
  }
  let bestMatches := hits.takeWhile (·.1 == best.1)
  if best.1 ≤ 3 && bestMatches.size == 1 then
    return best.2
  if best.1 ≤ 3 then
    throw {
      message := s!"ambiguous declaration '{query}'"
      candidates := suggestions
    }
  throw {
    message := s!"unknown declaration '{query}'"
    candidates := suggestions
  }

private def rawRelationLt (left right : RawRelation) : Bool :=
  left.distance < right.distance ||
    (left.distance == right.distance && Name.quickLt left.name right.name)

private def collectUpstream (env : Environment) (target : Name) (depth : Nat)
    (includeInternal : Bool) : Array RawRelation := Id.run do
  let mut visited : NameSet := ({} : NameSet).insert target
  let mut frontier := #[target]
  let mut results := #[]
  for distance in [1:depth + 1] do
    let mut next := #[]
    for parent in frontier do
      if let some info := env.find? parent then
        for dependency in info.getUsedConstantsAsSet do
          if !visited.contains dependency then
            visited := visited.insert dependency
            next := next.push dependency
            if visibleName includeInternal dependency then
              results := results.push {
                name := dependency
                distance
                via := if distance == 1 then none else some parent
              }
    frontier := next
    if frontier.isEmpty then
      break
  return results.qsort rawRelationLt

private def firstUsedConstant (targets : NameSet) (expr : Expr) : Option Name :=
  expr.foldConsts none fun name found =>
    match found with
    | some _ => found
    | none => if targets.contains name then some name else none

private def firstUsedName (targets : NameSet) : List Name → Option Name
  | [] => none
  | name :: names =>
    if targets.contains name then some name else firstUsedName targets names

/--
Returns one direct dependency in `targets`, if present. This avoids materializing a dependency
set for every declaration during a reverse scan.
-/
private def firstDependencyIn (targets : NameSet) (info : ConstantInfo) : Option Name :=
  match firstUsedConstant targets info.type with
  | some name => some name
  | none =>
    match info.value? (allowOpaque := true) with
    | some value => firstUsedConstant targets value
    | none =>
      match info with
      | .inductInfo value => firstUsedName targets value.ctors
      | .ctorInfo value =>
        if targets.contains value.name then some value.name else none
      | .recInfo value => firstUsedName targets value.all
      | _ => none

/--
Collect downstream declarations without retaining a global reverse adjacency map. Each requested
layer is one linear environment scan; the default depth of one therefore has bounded auxiliary
memory and a single scan.
-/
private def collectDownstream (env : Environment) (target : Name) (depth : Nat)
    (includeInternal : Bool) : Array RawRelation := Id.run do
  let mut visited : NameSet := ({} : NameSet).insert target
  let mut frontier : NameSet := ({} : NameSet).insert target
  let mut results := #[]
  for distance in [1:depth + 1] do
    let mut next : NameSet := {}
    for (name, info) in env.constants do
      if !visited.contains name then
        if let some via := firstDependencyIn frontier info then
          visited := visited.insert name
          next := next.insert name
          if visibleName includeInternal name then
            results := results.push {
              name
              distance
              via := if distance == 1 then none else some via
            }
    frontier := next
    if frontier.isEmpty then
      break
  return results.qsort rawRelationLt

private def moduleOf? (env : Environment) (name : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? name
  env.allImportedModuleNames[moduleIdx]?

private def ileanPath? (moduleName : Name) : IO (Option System.FilePath) := do
  try
    let path := (← findOLean moduleName).withExtension "ilean"
    return if ← path.pathExists then some path else none
  catch _ =>
    return none

private def loadIlean? (moduleName : Name) : IO (Option Server.Ilean) := do
  let some path ← ileanPath? moduleName | return none
  return some (← Server.Ilean.load path)

private def sourceDependencies (ilean : Server.Ilean) (parent : Name) : NameSet := Id.run do
  let parentName := nameString parent
  let mut dependencies : NameSet := {}
  for (ident, info) in ilean.references do
    let .const _ dependencyName := ident | continue
    if info.usages.any fun usage => usage.parentDecl? == some parentName then
      dependencies := dependencies.insert dependencyName.toName
  return dependencies

/-- Follow resolved source references inside the `.ilean` that owns each declaration. -/
private def collectSourceUpstream (env : Environment) (target : Name) (depth : Nat)
    (includeInternal : Bool) : CoreM (Array RawRelation) := do
  let mut cache : NameMap Server.Ilean := {}
  let mut visited : NameSet := ({} : NameSet).insert target
  let mut frontier := #[target]
  let mut results := #[]
  for distance in [1:depth + 1] do
    let mut next := #[]
    for parent in frontier do
      let some moduleName := moduleOf? env parent | continue
      let ilean? ← match cache.find? moduleName with
        | some ilean => pure (some ilean)
        | none => do
          let loaded ← loadIlean? moduleName
          if let some ilean := loaded then
            cache := cache.insert moduleName ilean
          pure loaded
      let some ilean := ilean? | continue
      for dependency in sourceDependencies ilean parent do
        if env.contains dependency && !visited.contains dependency then
          visited := visited.insert dependency
          next := next.push dependency
          if visibleName includeInternal dependency then
            results := results.push {
              name := dependency
              distance
              via := if distance == 1 then none else some parent
            }
    frontier := next
    if frontier.isEmpty then
      break
  return results.qsort rawRelationLt

private structure SourceTarget where
  name : Name
  ident : Lsp.RefIdent
  keyText : String

private def sourceTargets (env : Environment) (frontier : NameSet) : Array SourceTarget := Id.run do
  let mut targets := #[]
  for name in frontier do
    let some moduleName := moduleOf? env name | continue
    let ident := Lsp.RefIdent.const (nameString moduleName) (nameString name)
    -- `.ilean` encodes `RefIdent` as a JSON object serialized again as an object key.
    let keyText := (Json.str (toJson ident).compress).compress ++ ":"
    targets := targets.push { name, ident, keyText }
  return targets

private def sourceCandidateModules (env : Environment) (target : Name) : Array Name := Id.run do
  let modules := env.allImportedModuleNames
  let some targetIdx := env.getModuleIdxFor? target | return modules
  let targetIdx := targetIdx.toNat
  let some targetModule := modules[targetIdx]? | return modules
  let mut reachable : NameSet := ({} : NameSet).insert targetModule
  let mut candidates := #[targetModule]
  -- Imported modules are topologically ordered, so a single pass computes module-level dependents.
  for index in [targetIdx + 1:modules.size] do
    let some moduleName := modules[index]? | continue
    let some moduleData := env.header.moduleData[index]? | continue
    if moduleData.imports.any fun imported => reachable.contains imported.module then
      reachable := reachable.insert moduleName
      candidates := candidates.push moduleName
  return candidates

private def loadIleanContaining? (path : System.FilePath) (targets : Array SourceTarget) :
    IO (Option Server.Ilean) := do
  let content ← IO.FS.readFile path
  if targets.any fun target => content.contains target.keyText then
    return some (← Server.Ilean.load path)
  return none

private def scanIleanModule (moduleName : Name) (targets : Array SourceTarget) :
    IO (Option (Name × Server.Ilean)) := do
  let some path ← ileanPath? moduleName | return none
  let some ilean ← loadIleanContaining? path targets | return none
  return some (moduleName, ilean)

/-- Read `.ilean` files in bounded parallel batches to avoid serial filesystem latency. -/
private partial def scanIleanModules (modules : Array Name) (targets : Array SourceTarget)
    (offset : Nat := 0) (results : Array (Name × Server.Ilean) := #[]) :
    IO (Array (Name × Server.Ilean)) := do
  if offset >= modules.size then
    return results
  let stop := min (offset + 128) modules.size
  let mut tasks : Array (Task (Except IO.Error (Option (Name × Server.Ilean)))) := #[]
  for moduleName in modules.extract offset stop do
    tasks := tasks.push (← IO.asTask (scanIleanModule moduleName targets))
  let mut results := results
  let mut firstError? : Option IO.Error := none
  for task in tasks do
    match ← IO.wait task with
    | .ok (some result) => results := results.push result
    | .ok none => pure ()
    | .error error =>
      if firstError?.isNone then
        firstError? := some error
  match firstError? with
  | some error => throw error
  | none => scanIleanModules modules targets stop results

/--
Find declarations with source references to the frontier. Files are first checked for the exact
serialized reference key, and only matching `.ilean` files are parsed.
-/
private def collectSourceDownstream (env : Environment) (target : Name) (depth : Nat)
    (includeInternal : Bool) : CoreM (Array RawRelation) := do
  let candidateModules := sourceCandidateModules env target
  let mut visited : NameSet := ({} : NameSet).insert target
  let mut frontier : NameSet := ({} : NameSet).insert target
  let mut results := #[]
  for distance in [1:depth + 1] do
    let targets := sourceTargets env frontier
    if targets.isEmpty then
      break
    let mut next : NameSet := {}
    for (_, ilean) in (← scanIleanModules candidateModules targets) do
      for sourceTarget in targets do
        let some info := ilean.references.get? sourceTarget.ident | continue
        for usage in info.usages do
          let some parentName := usage.parentDecl? | continue
          let parent := parentName.toName
          if env.contains parent && !visited.contains parent then
            visited := visited.insert parent
            next := next.insert parent
            if visibleName includeInternal parent then
              results := results.push {
                name := parent
                distance
                via := if distance == 1 then none else some sourceTarget.name
              }
    frontier := next
    if frontier.isEmpty then
      break
  return results.qsort rawRelationLt

private def parentN (path : System.FilePath) : Nat → Option System.FilePath
  | 0 => some path
  | count + 1 => path.parent.bind fun parent => parentN parent count

/--
Build a source search path from both `LEAN_SRC_PATH` and Lake's `.olean` roots. Lake reliably sets
`LEAN_PATH` for executables, but does not set `LEAN_SRC_PATH` on every platform.
-/
private def sourceSearchPath : IO SearchPath := do
  let mut sources ← getSrcSearchPath
  for oleanRoot in (← searchPathRef.get) do
    -- Lake package/project layout: ROOT/.lake/build/lib/lean
    if let some packageRoot := parentN oleanRoot 4 then
      sources := sources ++ [packageRoot]
    -- Lean toolchain layout: SYSROOT/lib/lean -> SYSROOT/src/lean
    if let some sysroot := parentN oleanRoot 2 then
      sources := sources ++ [sysroot / "src" / "lean"]
  return sources

private def sourceLocation (sourcePath : SearchPath) (name : Name) : CoreM SourceLocation := do
  let moduleName? ← findModuleOf? name
  let file? ← match moduleName? with
    | some moduleName => sourcePath.findModuleWithExt "lean" moduleName
    | none => pure none
  let ranges? ← findDeclarationRanges? name
  let (line?, column?, endLine?, endColumn?) := match ranges? with
    | some ranges =>
      (some ranges.selectionRange.pos.line,
       some (ranges.selectionRange.pos.column + 1),
       some ranges.selectionRange.endPos.line,
       some (ranges.selectionRange.endPos.column + 1))
    | none => (none, none, none, none)
  return {
    moduleName := moduleName?.map nameString
    file := file?.map (·.toString)
    line := line?
    column := column?
    endLine := endLine?
    endColumn := endColumn?
  }

private def describeDeclaration (sourcePath : SearchPath) (name : Name) : CoreM DeclarationView := do
  let env ← getEnv
  let some kind := getOriginalConstKind? env name |
    throwError "declaration disappeared from the environment: {name}"
  return {
    name := nameString name
    kind := constantKind kind
    source := ← sourceLocation sourcePath name
  }

private def describeRelations (sourcePath : SearchPath) (limit : Nat)
    (relations : Array RawRelation) : CoreM RelationList := do
  let mut items := #[]
  for relation in relations.take limit do
    items := items.push {
      distance := relation.distance
      via := relation.via.map nameString
      declaration := ← describeDeclaration sourcePath relation.name
    }
  return { total := relations.size, items }

/-- Resolve a declaration and inspect its bounded dependency neighborhood. -/
def runQuery (config : QueryConfig) : CoreM (Except QueryFailure QueryResult) := do
  let env ← getEnv
  let sourcePath ← sourceSearchPath
  match resolveName env config.query config.includeInternal with
  | .error failure => do
    let mut candidates := #[]
    for name in failure.candidates do
      candidates := candidates.push (← describeDeclaration sourcePath name)
    return .error {
      error := failure.message
      candidates
    }
  | .ok target => do
    let upstream ←
      if config.direction.includesUpstream then
        match config.mode with
        | .source => collectSourceUpstream env target config.depth config.includeInternal
        | .kernel => pure <| collectUpstream env target config.depth config.includeInternal
      else
        pure #[]
    let downstream ←
      if config.direction.includesDownstream then
        match config.mode with
        | .source => collectSourceDownstream env target config.depth config.includeInternal
        | .kernel => pure <| collectDownstream env target config.depth config.includeInternal
      else
        pure #[]
    return .ok {
      query := config.query
      mode := config.mode.label
      target := ← describeDeclaration sourcePath target
      upstream := ← describeRelations sourcePath config.limit upstream
      downstream := ← describeRelations sourcePath config.limit downstream
    }

/-- Search declaration names using exact, suffix, case-insensitive, then substring ranking. -/
def runSearch (query : String) (limit : Nat) (includeInternal : Bool) : CoreM SearchResult := do
  let env ← getEnv
  let sourcePath ← sourceSearchPath
  let hits := scoredNames env query includeInternal
  let mut items := #[]
  for (_, name) in hits.take limit do
    items := items.push (← describeDeclaration sourcePath name)
  return {
    query
    total := hits.size
    items
  }

end LeanReach
