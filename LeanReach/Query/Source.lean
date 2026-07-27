import Lean.Data.Json
import Lean.Server.References
import Lean.Util.Path
import LeanReach.Query.Context
import LeanReach.Query.Ilean

namespace LeanReach.Query

open Lean Lean.Core

private def moduleOf? (env : Environment) (name : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? name
  env.allImportedModuleNames[moduleIdx]?

/-- Follow resolved source references inside the `.ilean` that owns each declaration. -/
def collectSourceUpstream (target : Name) : RequestM (Array RawRelation) := do
  let env ← getEnv
  let options ← read
  let mut cache : NameMap Server.Ilean := {}
  let mut visited : NameSet := ({} : NameSet).insert target
  let mut frontier := #[target]
  let mut results := #[]
  for distance in [1:options.depth + 1] do
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
          if visibleName options.includeInternal dependency then
            results := results.push {
              declaration := dependency
              distance
              via := if distance == 1 then none else some parent
            }
    frontier := next
    if frontier.isEmpty then
      break
  return results.qsort rawRelationLt

private abbrev SourceTarget := Name × Lsp.RefIdent × String

private def sourceTargets (frontier : NameSet) : RequestM (Array SourceTarget) := do
  let env ← getEnv
  return Id.run do
    let mut targets := #[]
    for name in frontier do
      let some moduleName := moduleOf? env name | continue
      let ident := Lsp.RefIdent.const (nameString moduleName) (nameString name)
      -- `.ilean` encodes `RefIdent` as a JSON object serialized again as an object key.
      let keyText := (Json.str (toJson ident).compress).compress ++ ":"
      targets := targets.push (name, ident, keyText)
    return targets

private def sourceCandidateModules (target : Name) : RequestM (Array Name) := do
  let env ← getEnv
  return Id.run do
    let modules := env.allImportedModuleNames
    let some targetIdx := env.getModuleIdxFor? target | return modules
    let targetIdx := targetIdx.toNat
    let some targetModule := modules[targetIdx]? | return modules
    let mut reachable : NameSet := ({} : NameSet).insert targetModule
    let mut candidates := #[targetModule]
    -- Imported modules are topologically ordered, so one pass computes module-level dependents.
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
  if targets.any fun (_, _, keyText) => content.contains keyText then
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
def collectSourceDownstream (target : Name) : RequestM (Array RawRelation) := do
  let env ← getEnv
  let options ← read
  let candidateModules ← sourceCandidateModules target
  let mut visited : NameSet := ({} : NameSet).insert target
  let mut frontier : NameSet := ({} : NameSet).insert target
  let mut results := #[]
  for distance in [1:options.depth + 1] do
    let targets ← sourceTargets frontier
    if targets.isEmpty then
      break
    let mut next : NameSet := {}
    for (_, ilean) in (← scanIleanModules candidateModules targets) do
      for (sourceName, ident, _) in targets do
        let some info := ilean.references.get? ident | continue
        for usage in info.usages do
          let some parentName := usage.parentDecl? | continue
          let parent := parentName.toName
          if env.contains parent && !visited.contains parent then
            visited := visited.insert parent
            next := next.insert parent
            if visibleName options.includeInternal parent then
              results := results.push {
                declaration := parent
                distance
                via := if distance == 1 then none else some sourceName
              }
    frontier := next
    if frontier.isEmpty then
      break
  return results.qsort rawRelationLt

end LeanReach.Query
