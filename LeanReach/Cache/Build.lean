import Init.System.Promise
import LeanReach.Cache.Index
import LeanReach.Cache.PrettyPrint
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

private unsafe def saveModule (moduleName : Name) (added : NameMap Declaration) :
    IO (Nat × Nat) := do
  let started ← IO.monoNanosNow
  unsafe Cache.mergePPModule moduleName added
  return (added.size, (← IO.monoNanosNow) - started)

private unsafe def addMissingInput (inputs : Array Input)
    (moduleName : Name) (names : Array Name) : IO (Array Input) := do
  let before ← unsafe Cache.loadPPModule moduleName
  let missing := names.filter fun name =>
    (before.find? name).all (!·.hasSource)
  return if missing.isEmpty then inputs else inputs.push (moduleName, missing)

private unsafe def completedModules (roots : Array Name) : IO NameHashSet := do
  let mut completed : NameHashSet := {}
  for root in roots do
    if ← unsafe Cache.isFullyPP #[root] then
      for moduleName in (← unsafe Cache.loadIndex #[root] false).modules do
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
      let (count, writeNanos) ← unsafe saveModule moduleName added
      pure <| .ok (count, { timing with sidecarWriteNanos := writeNanos })
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

unsafe def buildPPModules (modules : Array Name) : IO (Nat × PPTiming) := do
  let sourcePath ← prepareEnvironment
  let mut inputs : Array Input := #[]
  let mut seen : NameHashSet := {}
  for moduleName in modules do
    unless seen.contains moduleName do
      seen := seen.insert moduleName
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
      for (moduleName, declarations) in ← unsafe Cache.moduleClosure roots completed do
        inputs ← unsafe addMissingInput inputs moduleName (declarations.map (·.1))
      pure (inputs, fun _ => none)
  let report := fun moduleName done => progress moduleName done inputs.size
  let (count, timing) ←
    if let some envTask := envTask? then
      let (env, importNanos) ← IO.ofExcept envTask.get
      let (count, timing) ←
        unsafe buildModules sourcePath env inputs moduleOf? report
      pure (count, { timing with importNanos })
    else
      unsafe buildInputs sourcePath inputs roots moduleOf? report
  unsafe Cache.markFullyPP roots
  return (count, timing)

end LeanReach
