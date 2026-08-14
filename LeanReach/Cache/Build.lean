import Init.System.Promise
import LeanReach.Cache.Index
import LeanReach.Cache.PrettyPrint
import LeanReach.Cache.Progress
import LeanReach.Cache.Query
import LeanReach.PrettyPrint.Module
import LeanReach.Runtime.Environment

namespace LeanReach

open Lean

private abbrev Input := Name × Array Name
private abbrev Output := Name × Except IO.Error (Nat × PPTiming)

private def parallelism : IO Nat := do
  let some value ← IO.getEnv "LEANREACH_PP_JOBS" | return 4
  let some workers := value.toNat? | return 4
  return max 1 (min workers 32)

private unsafe def addMissingInput (inputs : Array Input)
    (moduleName : Name) (names : Array Name) : IO (Array Input) := do
  let before ← unsafe Cache.loadPPModule moduleName
  let missing := Declaration.missingFrom before names
  return if missing.isEmpty then inputs else inputs.push (moduleName, missing)

private unsafe def completedModules (roots : Array Name) : IO NameHashSet := do
  let mut completed : NameHashSet := {}
  for root in roots do
    if ← unsafe Cache.isFullyPP #[root] then
      if let some table ← unsafe SearchCache.loadTable #[root] then
        for moduleName in table.modules do
          completed := completed.insert moduleName
  return completed

private unsafe def worker (sourcePath : SearchPath) (env : Environment)
    (inputs : Array Input) (moduleOf? : Name → Option Name)
    (next finished : IO.Ref Nat) (outputs : Array (IO.Promise Output)) : IO Unit := do
  while true do
    let index ← next.modifyGet fun index => (index, index + 1)
    let some (moduleName, names) := inputs[index]? | return
    let result ← try
      let (added, timing) ← unsafe prettyPrintModuleIO
        sourcePath env moduleName names moduleOf?
      let started ← IO.monoNanosNow
      unsafe Cache.mergePPModule moduleName added
      pure <| .ok (added.size, {
        timing with sidecarWriteNanos := (← IO.monoNanosNow) - started
      })
    catch error => pure (.error error)
    let slot ← finished.modifyGet fun slot => (slot, slot + 1)
    let some output := outputs[slot]? | unreachable!
    output.resolve (moduleName, result)

private unsafe def buildModules (sourcePath : SearchPath) (env : Environment)
    (inputs : Array Input) (moduleOf? : Name → Option Name := fun _ => none)
    (progress : Name → Nat → IO Unit := fun _ _ => pure ()) :
    IO (Nat × PPTiming) := do
  if inputs.isEmpty then return (0, {})
  let workers := min (← parallelism) inputs.size
  let next ← IO.mkRef 0
  let finished ← IO.mkRef 0
  let outputs : Array (IO.Promise Output) ← inputs.mapM fun _ => IO.Promise.new
  let tasks ← (Array.range workers).mapM fun _ =>
    IO.asTask <| unsafe worker sourcePath env inputs moduleOf? next finished outputs
  let mut count := 0
  let mut timing := {}
  let mut failure? := none
  for (output, done) in outputs.zipIdx do
    let (moduleName, result) ← IO.wait output.result!
    match result with
    | .ok (added, elapsed) =>
      count := count + added
      timing := timing + elapsed
      progress moduleName (done + 1)
    | .error error =>
      if failure?.isNone then failure? := some error
  for task in tasks do IO.ofExcept (← IO.wait task)
  if let some error := failure? then throw error
  return (count, timing)

private unsafe def timedImport (modules : Array Name) : IO (Environment × Nat) := do
  let started ← IO.monoNanosNow
  let env ← importEnvironment modules (leakEnv := true)
  return (env, (← IO.monoNanosNow) - started)

private unsafe def buildInputs (sourcePath : SearchPath) (inputs : Array Input)
    (imports : Array Name := inputs.map (·.1))
    (moduleOf? : Name → Option Name := fun _ => none)
    (progress : Name → Nat → IO Unit := fun _ _ => pure ()) :
    IO (Nat × PPTiming) := do
  if inputs.isEmpty then return (0, {})
  let (env, importNanos) ← unsafe timedImport imports
  let (count, timing) ← unsafe buildModules sourcePath env inputs moduleOf? progress
  return (count, { timing with importNanos })

unsafe def buildPPModules (modules : Array Name)
    (progress : Cache.ProgressReporter := Cache.ignoreProgress) : IO (Nat × PPTiming) := do
  let sourcePath ← prepareEnvironment
  let mut inputs : Array Input := #[]
  let mut seen : NameHashSet := {}
  progress.count .planningPrettyPrint 0 modules.size
  for (moduleName, position) in modules.zipIdx do
    unless seen.contains moduleName do
      seen := seen.insert moduleName
      inputs ← unsafe addMissingInput inputs moduleName (← unsafe Cache.moduleNames moduleName)
    progress.count .planningPrettyPrint (position + 1) modules.size
      (some moduleName.toString)
  progress.count .prettyPrinting 0 inputs.size
  let result ← unsafe buildInputs sourcePath inputs (progress := fun moduleName done =>
    progress.count .prettyPrinting done inputs.size (some moduleName.toString))
  progress.count .prettyPrinting inputs.size inputs.size
  return result

/-- Pretty-print every declaration below a root, checkpointing once per defining module. -/
unsafe def buildPPRoots (roots : Array Name)
    (progress : Cache.ProgressReporter := Cache.ignoreProgress) :
    IO (Nat × PPTiming) := do
  progress.count .preparing 0 1
  let sourcePath ← prepareEnvironment
  let ppReady ← unsafe Cache.isFullyPP roots
  let queryReady ← unsafe QueryCache.isBuilt roots
  progress.count .preparing 1 1
  if ppReady && queryReady then return (0, {})
  let completed : NameHashSet ←
    if ppReady then pure {} else unsafe completedModules roots
  let envTask? ←
    if !ppReady && !queryReady && completed.isEmpty then
      some <$> IO.asTask (unsafe timedImport roots)
    else pure none
  unless queryReady do discard <| unsafe QueryCache.build roots progress
  if ppReady then return (0, {})
  let (inputs, moduleOf?) : Array Input × (Name → Option Name) ←
    if completed.isEmpty then
      let some table ← unsafe SearchCache.loadTable roots |
        throw <| IO.userError "declaration table is unavailable"
      let mut inputs := #[]
      let modules := table.declarationsByModule.toArray
      progress.count .planningPrettyPrint 0 modules.size
      for ((moduleName, names), position) in modules.zipIdx do
        inputs ← unsafe addMissingInput inputs moduleName names
        progress.count .planningPrettyPrint (position + 1) modules.size
          (some moduleName.toString)
      pure (inputs, table.moduleOf?)
    else
      let mut inputs := #[]
      let modules ← unsafe Cache.moduleClosure roots completed progress
      progress.count .planningPrettyPrint 0 modules.size
      for ((moduleName, declarations), position) in modules.zipIdx do
        inputs ← unsafe addMissingInput inputs moduleName (declarations.map (·.1))
        progress.count .planningPrettyPrint (position + 1) modules.size
          (some moduleName.toString)
      pure (inputs, fun _ => none)
  let report := fun moduleName done =>
    progress.count .prettyPrinting done inputs.size (some moduleName.toString)
  progress.count .prettyPrinting 0 inputs.size
  let (count, timing) ←
    if let some envTask := envTask? then
      let (env, importNanos) ← IO.ofExcept envTask.get
      let (count, timing) ←
        unsafe buildModules sourcePath env inputs moduleOf? report
      pure (count, { timing with importNanos })
    else
      unsafe buildInputs sourcePath inputs roots moduleOf? report
  unsafe Cache.markFullyPP roots
  progress.count .prettyPrinting inputs.size inputs.size
  return (count, timing)

end LeanReach
