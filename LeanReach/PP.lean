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
    (inputs : Array Input)
    (progress : Name → NameMap Declaration → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  let workers ← parallelism
  let mut count := 0
  let mut offset := 0
  while offset < inputs.size do
    let stop := min inputs.size (offset + workers)
    let batch := inputs.extract offset stop
    let tasks ← batch.mapM fun (moduleName, names, _) =>
      IO.asTask (unsafe runCore env (prettyPrintModule sourcePath moduleName names))
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
  let env ← importEnvironment (inputs.map fun (module, _, _) => module)
    (leakEnv := true) (level := .private)
  unsafe buildModules sourcePath env inputs

private def fillBundle (index : Index) (slots : Array (Option Declaration))
    (declarations : NameMap Declaration) : Array (Option Declaration) := Id.run do
  let mut slots := slots
  for (name, declaration) in declarations do
    if let some id := index.idOf? name then
      slots := slots.set! id.toNat (some declaration)
  return slots

/-- Pretty-print every declaration below a root, checkpointing once per defining module. -/
unsafe def buildPPRoots (roots : Array Name)
    (progress : Name → Nat → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  let sourcePath ← prepareEnvironment
  let index ← unsafe Cache.loadIndex roots false
  if ← unsafe Cache.isFullyPP roots then
    unless (← unsafe Cache.loadPPBundle roots index).isEmpty do return 0
  let mut slots : Array (Option Declaration) := Array.replicate index.size none
  let mut inputs : Array Input := #[]
  for (moduleName, names) in index.declarationsByModule do
    let before ← unsafe Cache.loadPPModule moduleName
    slots := fillBundle index slots before
    let missing := names.filter fun name => !before.contains name
    unless missing.isEmpty do
      inputs := inputs.push (moduleName, missing, before)
  let mut count := 0
  unless inputs.isEmpty do
    let env ← importEnvironment (inputs.map fun (module, _, _) => module)
      (leakEnv := true) (level := .private)
    let slotsRef ← IO.mkRef slots
    count ← unsafe buildModules sourcePath env inputs fun moduleName added done => do
      slotsRef.modify fun slots => fillBundle index slots added
      progress moduleName done inputs.size
    slots ← slotsRef.get
  let declarations ← slots.mapM fun
    | some declaration => pure declaration
    | none => throw <| IO.userError "PP bundle is incomplete"
  unsafe Cache.savePPBundle roots declarations
  unsafe Cache.markFullyPP roots
  return count

end LeanReach
