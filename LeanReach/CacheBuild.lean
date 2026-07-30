import Std.Sync.Channel
import LeanReach.IndexCache
import LeanReach.ModuleData
import LeanReach.PPCache
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
    IO (Nat × Nat) := do
  let started ← IO.monoNanosNow
  unsafe Cache.savePPModule moduleName (Std.TreeMap.union before added)
  return (added.size, (← IO.monoNanosNow) - started)

private unsafe def addMissingInput (inputs : Array Input)
    (moduleName : Name) (names : Array Name) : IO (Array Input) := do
  let before ← unsafe Cache.loadPPModule moduleName
  let missing := names.filter fun name => !before.contains name
  return if missing.isEmpty then inputs else inputs.push (moduleName, missing, before)

private unsafe def completedModules (roots : Array Name) : IO NameHashSet := do
  let mut completed : NameHashSet := {}
  for root in roots do
    if ← unsafe Cache.isFullyPP #[root] then
      for moduleName in (← unsafe Cache.loadIndex #[root] false).modules do
        completed := completed.insert moduleName
  return completed

unsafe def prettyPrintModuleIO (sourcePath : SearchPath) (env : Environment)
    (moduleName : Name) (names : Array Name) (moduleOf? : Name → Option Name) :
    IO (NameMap Declaration × PPTiming) := do
  let preparationStarted ← IO.monoNanosNow
  let source ← moduleSource sourcePath moduleName
  let (bodies, signatureOverlay) ← unsafe runCore env (prettyPrintPlan names)
  let bodySet := bodies.foldl (init := ({} : NameHashSet))
    fun result name => result.insert name
  let preparationNanos := (← IO.monoNanosNow) - preparationStarted
  let print := fun env =>
    unsafe runCore env (prettyPrintModuleWithBodies moduleName source names bodySet)
  let ((declarations, timing), overlayNanos) ←
    if signatureOverlay.isEmpty && bodies.isEmpty then
      pure ((← print env), 0)
    else
      unsafe ModuleData.withPrivateOverlay env moduleName
        signatureOverlay bodies moduleOf? print
  return (declarations, {
    timing with
    privateOverlayNanos := overlayNanos
    signatureNanos := timing.signatureNanos + preparationNanos
  })

private unsafe def worker (sourcePath : SearchPath) (env : Environment)
    (moduleOf? : Name → Option Name) (jobs : Std.Channel.Sync (Option Input))
    (results : Std.Channel.Sync
      (Option (Name × Except IO.Error (Nat × PPTiming)))) : IO Unit := do
  while true do
    let some (moduleName, names, before) ← jobs.recv | return
    let result ← try
      let (added, timing) ← unsafe prettyPrintModuleIO
        sourcePath env moduleName names moduleOf?
      let (count, writeNanos) ← unsafe saveModule moduleName before added
      pure <| .ok (count, { timing with sidecarWriteNanos := writeNanos })
    catch error => pure (.error error)
    results.send (some (moduleName, result))

private unsafe def buildModules (sourcePath : SearchPath) (env : Environment)
    (inputs : Array Input) (moduleOf? : Name → Option Name := fun _ => none)
    (progress : Name → Nat → IO Unit := fun _ _ => pure ()) :
    IO (Nat × PPTiming) := do
  if inputs.isEmpty then return (0, {})
  let workers := min (← parallelism) inputs.size
  let jobs ← Std.Channel.Sync.new
  let results ← Std.Channel.Sync.new
  for input in inputs do jobs.send (some input)
  for _ in [0:workers] do jobs.send none
  let tasks ← (Array.range workers).mapM fun _ =>
    IO.asTask <| unsafe worker sourcePath env moduleOf? jobs results
  let mut count := 0
  let mut timing := {}
  let mut failure? := none
  for done in [0:inputs.size] do
    let some (moduleName, result) ← results.recv | unreachable!
    match result with
    | .ok (added, elapsed) =>
      count := count + added
      timing := timing + elapsed
      progress moduleName (done + 1)
    | .error error =>
      if failure?.isNone then failure? := some error
  for task in tasks do IO.ofExcept task.get
  if let some error := failure? then throw error
  return (count, timing)

private unsafe def timedImport (modules : Array Name) : IO (Environment × Nat) := do
  let started ← IO.monoNanosNow
  let env ← importEnvironment modules (leakEnv := true)
  return (env, (← IO.monoNanosNow) - started)

private unsafe def buildInputs (sourcePath : SearchPath) (inputs : Array Input)
    (moduleOf? : Name → Option Name := fun _ => none)
    (progress : Name → Nat → IO Unit := fun _ _ => pure ()) :
    IO (Nat × PPTiming) := do
  if inputs.isEmpty then return (0, {})
  let (env, importNanos) ← unsafe timedImport (inputs.map (·.1))
  let (count, timing) ← unsafe buildModules sourcePath env inputs moduleOf? progress
  return (count, { timing with importNanos })

unsafe def buildPPModules (modules : Array Name) : IO (Nat × PPTiming) := do
  let sourcePath ← prepareEnvironment
  let mut inputs : Array Input := #[]
  for moduleName in modules do
    inputs ← unsafe addMissingInput inputs moduleName (← unsafe Cache.moduleNames moduleName)
  unsafe buildInputs sourcePath inputs

/-- Pretty-print every declaration below a root, checkpointing once per defining module. -/
unsafe def buildPPRoots (roots : Array Name)
    (progress : Name → Nat → Nat → IO Unit := fun _ _ _ => pure ()) :
    IO (Nat × PPTiming) := do
  let sourcePath ← prepareEnvironment
  let ppReady ← unsafe Cache.isFullyPP roots
  let queryReady ← unsafe QueryCache.isBuilt roots
  if ppReady && queryReady then return (0, {})
  let completed : NameHashSet ←
    if ppReady then pure {} else unsafe completedModules roots
  let envTask? ←
    if !ppReady && !queryReady && completed.isEmpty then
      some <$> IO.asTask (unsafe timedImport roots)
    else pure none
  unless queryReady do discard <| unsafe QueryCache.build roots
  if ppReady then return (0, {})
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
  let (count, timing) ←
    if let some envTask := envTask? then
      let (env, importNanos) ← IO.ofExcept envTask.get
      let (count, timing) ←
        unsafe buildModules sourcePath env inputs moduleOf? report
      pure (count, { timing with importNanos })
    else
      unsafe buildInputs sourcePath inputs moduleOf? report
  unsafe Cache.markFullyPP roots
  return (count, timing)

end LeanReach
