import LeanReach.Cache
import LeanReach.PrettyPrint
import LeanReach.Runtime

namespace LeanReach

open Lean

private unsafe def buildModule (sourcePath : SearchPath) (env : Environment)
    (moduleName : Name) (names : Array Name) (before : NameMap Declaration) : IO Nat := do
  let added ← unsafe runCore env (prettyPrintModule sourcePath moduleName names)
  let mut after := before
  for (name, declaration) in added do
    after := after.insert name declaration
  unsafe Cache.savePPModule moduleName after
  return added.size

unsafe def buildPPModules (modules : Array Name) : IO Nat := do
  let sourcePath ← prepareEnvironment
  let mut active := #[]
  let mut inputs : NameMap (Array Name × NameMap Declaration) := {}
  for moduleName in modules do
    let names ← unsafe Cache.moduleNames moduleName
    let before ← unsafe Cache.loadPPModule moduleName
    let missing := names.filter fun name => !before.contains name
    unless missing.isEmpty do
      active := active.push moduleName
      inputs := inputs.insert moduleName (missing, before)
  if active.isEmpty then return 0
  let env ← do
    Lean.enableInitializersExecution
    importModules (loadExts := true) (active.map fun module => { module }) {}
  let mut count := 0
  for moduleName in active do
    let (names, before) := (inputs.find? moduleName).getD (#[], {})
    count := count + (← unsafe buildModule sourcePath env moduleName names before)
  return count

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
    let mut inputs : NameMap (Array Name × NameMap Declaration) := {}
    for (moduleName, names) in pending do
      let before ← unsafe Cache.loadPPModule moduleName
      let missing := names.filter fun name => !before.contains name
      unless missing.isEmpty do
        inputs := inputs.insert moduleName (missing, before)
    let env? ←
      if inputs.isEmpty then pure none
      else
        Lean.enableInitializersExecution
        pure <| some (← importModules (loadExts := true)
          (roots.map fun module => { module }) {})
    for ((moduleName, _), done) in pending.zipIdx do
      if let some (names, before) := inputs.find? moduleName then
        let some env := env? |
          throw <| IO.userError "missing PP environment"
        count := count + (← unsafe buildModule sourcePath env moduleName names before)
      completed := completed.insert moduleName
      progress moduleName (done + 1) pending.size
      if done % 32 == 31 || done + 1 == pending.size then
        unsafe Cache.savePPProgress roots completed
  unsafe Cache.savePPBundle roots index
  unsafe Cache.markFullyPP roots
  return count

end LeanReach
