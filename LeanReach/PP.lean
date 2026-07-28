import LeanReach.Cache
import LeanReach.PrettyPrint
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
    (inputs : Array Input) (progress : Name → Nat → IO Unit := fun _ _ => pure ()) : IO Nat := do
  let workers ← parallelism
  let mut count := 0
  let mut offset := 0
  while offset < inputs.size do
    let stop := min inputs.size (offset + workers)
    let batch := inputs.extract offset stop
    let tasks ← batch.mapM fun (moduleName, names, _) =>
      IO.asTask (unsafe runCore env (prettyPrintModule sourcePath moduleName names))
    for (((moduleName, _, before), task), done) in (batch.zip tasks).zipIdx do
      count := count + (← unsafe saveModule moduleName before (← IO.ofExcept task.get))
      progress moduleName (offset + done + 1)
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
  let env ← do
    Lean.enableInitializersExecution
    importModules (loadExts := true) (inputs.map fun (module, _, _) => { module }) {}
  unsafe buildModules sourcePath env inputs

/-- Pretty-print every declaration below a root, checkpointing once per defining module. -/
unsafe def buildPPRoots (roots : Array Name)
    (progress : Name → Nat → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex roots false
  if ← unsafe Cache.isFullyPP roots then
    if (← unsafe Cache.loadPPBundle roots index).isEmpty then
      unsafe Cache.savePPBundle roots index
    return 0
  let mut completed ← unsafe Cache.loadPPProgress roots
  let mut pending := #[]
  for (moduleName, names) in index.declarationsByModule do
    unless completed.contains moduleName do
      pending := pending.push (moduleName, names)
  let mut count := 0
  unless pending.isEmpty do
    let mut inputs : Array Input := #[]
    for (moduleName, names) in pending do
      let before ← unsafe Cache.loadPPModule moduleName
      let missing := names.filter fun name => !before.contains name
      if missing.isEmpty then
        completed := completed.insert moduleName
      else
        inputs := inputs.push (moduleName, missing, before)
    unsafe Cache.savePPProgress roots completed
    unless inputs.isEmpty do
      Lean.enableInitializersExecution
      let env ← importModules (loadExts := true) (roots.map fun module => { module }) {}
      let completedRef ← IO.mkRef completed
      count ← unsafe buildModules sourcePath env inputs fun moduleName done => do
        completedRef.modify (·.insert moduleName)
        progress moduleName done inputs.size
        if done % 32 == 0 || done == inputs.size then
          unsafe Cache.savePPProgress roots (← completedRef.get)
  unsafe Cache.savePPBundle roots index
  unsafe Cache.markFullyPP roots
  return count

end LeanReach
