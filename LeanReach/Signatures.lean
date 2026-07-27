import Lean.Data.NameMap
import Lean.PrettyPrinter
import Lean.Util.Path
import LeanReach.Query.Context

namespace LeanReach.Signatures

open Lean

def unavailable (name : Name) : String :=
  s!"{Query.nameString name} : <signature unavailable>"

@[noinline] private unsafe def render (info : ConstantInfo) : IO String := do
  let env ← mkEmptyEnvironment (trustLevel := 1024)
  let added ← env.addConstAsync info.name (.ofConstantInfo info)
  added.commitConst added.asyncEnv (some info) (some info)
  added.commitCheckEnv added.asyncEnv
  let action := Meta.MetaM.run' (PrettyPrinter.ppSignature info.name)
  let signature ← Core.CoreM.toIO' action
    { fileName := "<leanreach>", fileMap := default }
    { env := added.mainEnv }
  return signature.fmt.pretty

@[noinline] private unsafe def extract (moduleData : ModuleData) (names : NameSet) :
    IO (NameMap String) := do
  let mut signatures := {}
  for name in names do
    if let some info := moduleData.constants.find? (·.name == name) then
      let signature ←
        try unsafe render info
        catch _ => pure (unavailable name)
      signatures := signatures.insert name signature
  return signatures

/--
Render selected exported constants from one `.olean` without importing its dependency environment.
The returned names and strings do not retain references into the mapped module data.
-/
unsafe def load (moduleName : Name) (names : NameSet) : IO (NameMap String) := do
  try
    let path ← findOLean moduleName
    let (moduleData, region) ← readModuleData path
    let signatures ←
      try unsafe extract moduleData names
      catch error =>
        unsafe region.free
        throw error
    unsafe region.free
    return signatures
  catch _ =>
    return {}

end LeanReach.Signatures
