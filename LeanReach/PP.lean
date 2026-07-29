import Std.Sync.Channel
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

private unsafe def addMissingInput (inputs : Array Input)
    (moduleName : Name) (names : Array Name) : IO (Array Input) :=
  return (← unsafe missingInput moduleName names).map inputs.push |>.getD inputs

private unsafe def completedModules (roots : Array Name) : IO NameHashSet := do
  let mut completed : NameHashSet := {}
  for root in roots do
    if ← unsafe Cache.isFullyPP #[root] then
      for moduleName in (← unsafe Cache.loadIndex #[root] false).modules do
        completed := completed.insert moduleName
  return completed

private unsafe def worker (sourcePath : SearchPath) (env : Environment)
    (moduleOf? : Name → Option Name) (jobs : Std.Channel.Sync (Option Input))
    (results : Std.Channel.Sync (Option (Name × Except IO.Error Nat))) : IO Unit := do
  while true do
    let some (moduleName, names, before) ← jobs.recv | return
    let result ← try
      let added ← unsafe Cache.withModuleConstants env moduleName names moduleOf? fun env =>
        unsafe runCore env (prettyPrintModule sourcePath moduleName names)
      .ok <$> unsafe saveModule moduleName before added
    catch error => pure (.error error)
    results.send (some (moduleName, result))

private unsafe def buildModules (sourcePath : SearchPath) (env : Environment)
    (inputs : Array Input) (moduleOf? : Name → Option Name := fun _ => none)
    (progress : Name → Nat → IO Unit := fun _ _ => pure ()) : IO Nat := do
  if inputs.isEmpty then return 0
  let workers := min (← parallelism) inputs.size
  let jobs ← Std.Channel.Sync.new
  let results ← Std.Channel.Sync.new
  for input in inputs do jobs.send (some input)
  for _ in [0:workers] do jobs.send none
  let tasks ← (Array.range workers).mapM fun _ =>
    IO.asTask <| unsafe worker sourcePath env moduleOf? jobs results
  let mut count := 0
  let mut failure? := none
  for done in [0:inputs.size] do
    let some (moduleName, result) ← results.recv | unreachable!
    match result with
    | .ok added =>
      count := count + added
      progress moduleName (done + 1)
    | .error error =>
      if failure?.isNone then failure? := some error
  for task in tasks do IO.ofExcept task.get
  if let some error := failure? then throw error
  return count

private unsafe def buildInputs (sourcePath : SearchPath) (inputs : Array Input)
    (moduleOf? : Name → Option Name := fun _ => none)
    (progress : Name → Nat → IO Unit := fun _ _ => pure ()) :
    IO Nat := do
  if inputs.isEmpty then return 0
  let env ← importEnvironment (inputs.map (·.1)) (leakEnv := true)
  unsafe buildModules sourcePath env inputs moduleOf? progress

unsafe def buildPPModules (modules : Array Name) : IO Nat := do
  let sourcePath ← prepareEnvironment
  let mut inputs : Array Input := #[]
  for moduleName in modules do
    inputs ← unsafe addMissingInput inputs moduleName (← unsafe Cache.moduleNames moduleName)
  unsafe buildInputs sourcePath inputs

/-- Pretty-print every declaration below a root, checkpointing once per defining module. -/
unsafe def buildPPRoots (roots : Array Name)
    (progress : Name → Nat → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  let sourcePath ← prepareEnvironment
  let ppReady ← unsafe Cache.isFullyPP roots
  let queryReady ← unsafe QueryCache.isBuilt roots
  if ppReady && queryReady then return 0
  let completed : NameHashSet ←
    if ppReady then pure {} else unsafe completedModules roots
  let envTask? ←
    if !ppReady && !queryReady && completed.isEmpty then
      some <$> IO.asTask (importEnvironment roots (leakEnv := true))
    else pure none
  unless queryReady do discard <| unsafe QueryCache.build roots
  if ppReady then return 0
  let (inputs, moduleOf?) : Array Input × (Name → Option Name) ←
    if completed.isEmpty then
      let index ← unsafe Cache.loadIndex roots false
      let mut inputs := #[]
      for (moduleName, names) in index.declarationsByModule do
        inputs ← unsafe addMissingInput inputs moduleName names
      pure (inputs, index.moduleOf?)
    else
      let mut inputs := #[]
      for moduleName in roots do
        unless completed.contains moduleName do
          inputs ← unsafe addMissingInput inputs moduleName
            (← unsafe Cache.moduleNames moduleName)
      pure (inputs, fun _ => none)
  let report := fun moduleName done => progress moduleName done inputs.size
  let count ←
    if let some envTask := envTask? then
      unsafe buildModules sourcePath (← IO.ofExcept envTask.get) inputs moduleOf? report
    else
      unsafe buildInputs sourcePath inputs moduleOf? report
  unsafe Cache.markFullyPP roots
  return count

end LeanReach
