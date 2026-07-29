import LeanReach.Cache
import LeanReach.PrettyPrint
import LeanReach.QueryCache
import LeanReach.Runtime

namespace LeanReach

open Lean

private abbrev Input := Name × Array Name × NameMap Declaration

private def parallelism : IO Nat := do
  let some value ← IO.getEnv "LEANREACH_PP_JOBS" | return 4
  let some workers := value.toNat? | return 4
  return max 1 (min workers 32)

private unsafe def saveModule (moduleName : Name) (before added : NameMap Declaration) :
    IO Nat := do
  let mut after := before
  for (name, declaration) in added do
    after := after.insert name declaration
  unsafe Cache.savePPModule moduleName after
  return added.size

private unsafe def missingInput (moduleName : Name) (names : Array Name) :
    IO (Option Input) := do
  let before ← unsafe Cache.loadPPModule moduleName
  let missing := names.filter fun name => !before.contains name
  return if missing.isEmpty then none else some (moduleName, missing, before)

private unsafe def completedModules (roots : Array Name) : IO NameHashSet := do
  let mut completed : NameHashSet := {}
  for root in roots do
    if ← unsafe Cache.isFullyPP #[root] then
      for moduleName in (← unsafe Cache.loadIndex #[root] false).modules do
        completed := completed.insert moduleName
  return completed

private unsafe def buildModules (sourcePath : SearchPath) (env : Environment)
    (inputs : Array Input) (moduleOf? : Name → Option Name := fun _ => none)
    (progress : Name → NameMap Declaration → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  let workers ← parallelism
  let mut count := 0
  let mut offset := 0
  while offset < inputs.size do
    let stop := min inputs.size (offset + workers)
    let batch := inputs.extract offset stop
    let tasks ← batch.mapM fun (moduleName, names, _) =>
      IO.asTask <| unsafe Cache.withModuleConstants env moduleName names moduleOf? fun env =>
        unsafe runCore env (prettyPrintModule sourcePath moduleName names)
    for (((moduleName, _, before), task), done) in (batch.zip tasks).zipIdx do
      let added ← IO.ofExcept task.get
      count := count + (← unsafe saveModule moduleName before added)
      progress moduleName added (offset + done + 1)
    offset := stop
  return count

private unsafe def buildInputs (sourcePath : SearchPath) (inputs : Array Input)
    (moduleOf? : Name → Option Name := fun _ => none)
    (progress : Name → NameMap Declaration → Nat → IO Unit := fun _ _ _ => pure ()) :
    IO Nat := do
  if inputs.isEmpty then return 0
  let env ← importEnvironment (inputs.map (·.1)) (leakEnv := true)
  unsafe buildModules sourcePath env inputs moduleOf? progress

unsafe def buildPPModules (modules : Array Name) : IO Nat := do
  let sourcePath ← prepareEnvironment
  let mut inputs : Array Input := #[]
  for moduleName in modules do
    let names ← unsafe Cache.moduleNames moduleName
    if let some input ← unsafe missingInput moduleName names then
      inputs := inputs.push input
  unsafe buildInputs sourcePath inputs

/-- Pretty-print every declaration below a root, checkpointing once per defining module. -/
unsafe def buildPPRoots (roots : Array Name)
    (progress : Name → Nat → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  let sourcePath ← prepareEnvironment
  let ppReady ← unsafe Cache.isFullyPP roots
  let queryReady ← unsafe QueryCache.isBuilt roots
  if ppReady && queryReady then return 0
  let envTask? ←
    if !ppReady && !queryReady then
      some <$> IO.asTask (importEnvironment roots (leakEnv := true))
    else pure none
  unless queryReady do discard <| unsafe QueryCache.build roots
  if ppReady then return 0
  let completed ← unsafe completedModules roots
  let (inputs, moduleOf?) : Array Input × (Name → Option Name) ←
    if completed.isEmpty then
      let index ← unsafe Cache.loadIndex roots false
      let mut inputs := #[]
      for (moduleName, names) in index.declarationsByModule do
        if let some input ← unsafe missingInput moduleName names then
          inputs := inputs.push input
      pure (inputs, index.moduleOf?)
    else
      let mut inputs := #[]
      for moduleName in roots do
        unless completed.contains moduleName do
          if let some input ← unsafe missingInput moduleName
              (← unsafe Cache.moduleNames moduleName) then
            inputs := inputs.push input
      pure (inputs, fun _ => none)
  let report := fun moduleName _ done => progress moduleName done inputs.size
  let count ←
    if let some envTask := envTask? then
      unsafe buildModules sourcePath (← IO.ofExcept envTask.get) inputs moduleOf? report
    else
      unsafe buildInputs sourcePath inputs moduleOf? report
  unsafe Cache.markFullyPP roots
  return count

end LeanReach
