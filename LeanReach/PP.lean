import LeanReach.Cache
import LeanReach.PrettyPrint
import LeanReach.Runtime

namespace LeanReach

open Lean

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
    let added ← unsafe runCore env (prettyPrintModule sourcePath moduleName names)
    let after := Id.run do
      let mut after := before
      for (name, declaration) in added do
        after := after.insert name declaration
      return after
    unsafe Cache.savePPModule moduleName after
    count := count + added.size
  return count

private def batchSize := 32

private def runWorker (executable : System.FilePath)
    (modules : Array Name) : IO Unit := do
  let output ← IO.Process.output {
    cmd := executable.toString
    args := #["cache"] ++ modules.map (·.toString) ++ #["--json"]
  }
  unless output.exitCode == 0 do
    throw <| IO.userError s!"failed to cache '{modules}': {output.stderr.trimAscii.copy}"

private unsafe def requireModule (moduleName : Name) (names : Array Name) :
    IO (NameMap Declaration) := do
  let declarations ← unsafe Cache.loadPPModule moduleName
  unless names.all declarations.contains do
    throw <| IO.userError s!"incomplete PP cache for '{moduleName}'"
  return declarations

/-- Pretty-print every declaration below a root, checkpointing once per defining module. -/
unsafe def buildPPRoots (roots : Array Name)
    (progress : Name → Nat → Nat → IO Unit := fun _ _ _ => pure ()) : IO Nat := do
  discard <| prepareEnvironment
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
    let executable ← IO.appPath
    let mut offset := 0
    while offset < pending.size do
      let stop := min pending.size (offset + batchSize)
      let batch := pending.extract offset stop
      let mut active := #[]
      let mut beforeSizes : NameMap Nat := {}
      for (moduleName, names) in batch do
        let before ← unsafe Cache.loadPPModule moduleName
        unless names.all before.contains do
          active := active.push moduleName
          beforeSizes := beforeSizes.insert moduleName before.size
      unless active.isEmpty do runWorker executable active
      for ((moduleName, names), done) in batch.zipIdx do
        if let some beforeSize := beforeSizes.find? moduleName then
          let after ← unsafe requireModule moduleName names
          count := count + after.size - beforeSize
        completed := completed.insert moduleName
        progress moduleName (offset + done + 1) pending.size
      unsafe Cache.savePPProgress roots completed
      offset := stop
  unsafe Cache.savePPBundle roots index
  unsafe Cache.markFullyPP roots
  return count

end LeanReach
