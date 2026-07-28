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

unsafe def buildPPModules (modules : Array Name) : IO Nat := do
  let sourcePath ← prepareEnvironment
  let mut inputs : Array Input := #[]
  for moduleName in modules do
    let names ← unsafe Cache.moduleNames moduleName
    let before ← unsafe Cache.loadPPModule moduleName
    let missing := names.filter fun name => !before.contains name
    unless missing.isEmpty do
      inputs := inputs.push (moduleName, missing, before)
  if inputs.isEmpty then return 0
  let env ← importEnvironment (inputs.map fun (module, _, _) => module) (leakEnv := true)
  unsafe buildModules sourcePath env inputs

/-- Pretty-print every declaration below a root, checkpointing once per defining module. -/
unsafe def buildPPRoots (roots : Array Name)
    (progress : Name → Nat → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  let sourcePath ← prepareEnvironment
  let ppReady ← unsafe Cache.isFullyPP roots
  let queryReady ← unsafe QueryCache.isBuilt roots
  if ppReady && queryReady then return 0
  let index ← unsafe Cache.loadIndex roots (!queryReady)
  unless queryReady do discard <| unsafe QueryCache.build roots index
  if ppReady then return 0
  let mut inputs : Array Input := #[]
  let mut envTask? := none
  for (moduleName, names) in index.declarationsByModule do
    let before ← unsafe Cache.loadPPModule moduleName
    let missing := names.filter fun name => !before.contains name
    unless missing.isEmpty do
      if envTask?.isNone then
        envTask? := some (← IO.asTask <| importEnvironment roots (leakEnv := true))
      inputs := inputs.push (moduleName, missing, before)
  let mut count := 0
  unless inputs.isEmpty do
    let some envTask := envTask? | unreachable!
    let env ← IO.ofExcept envTask.get
    count ← unsafe buildModules sourcePath env inputs index.moduleOf? fun moduleName _ done =>
      progress moduleName done inputs.size
  unsafe Cache.markFullyPP roots
  return count

end LeanReach
