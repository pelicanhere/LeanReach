import Lean.Data.NameMap
import Lean.PrettyPrinter
import Lean.Util.FoldConsts
import Lean.Util.Path
import LeanReach.Query.Context

namespace LeanReach.Signatures

open Lean

def unavailable (name : Name) : String :=
  s!"{Query.nameString name} : <signature unavailable>"

private unsafe def addConstant (env : Environment) (info : ConstantInfo) : IO Environment := do
  if env.contains info.name then
    return env
  let added ← env.addConstAsync info.name (.ofConstantInfo info)
  added.commitConst added.asyncEnv (some info) (some info)
  added.commitCheckEnv added.asyncEnv
  return added.mainEnv

private unsafe def render (env : Environment) (info : ConstantInfo) : IO String := do
  let action := Meta.MetaM.run' (PrettyPrinter.ppSignature info.name)
  let signature ← Core.CoreM.toIO' action
    { fileName := "<leanreach>", fileMap := default }
    { env }
  return signature.fmt.pretty

@[noinline] private def referencedConstants (moduleData : ModuleData) (names : NameSet) :
    NameSet := Id.run do
  let mut references := {}
  for info in moduleData.constants do
    if names.contains info.name then
      references := info.type.foldConsts references fun name found => found.insert name
  return references

@[noinline] private unsafe def renderParts
    (parts : Array (ModuleData × CompactedRegion)) (names references : NameSet) :
    IO (NameMap String × Array CompactedRegion) := do
  let regions := parts.map (·.2)
  try
    let mut env ← mkEmptyEnvironment (trustLevel := 1024)
    for (moduleData, _) in parts do
      for info in moduleData.constants do
        if names.contains info.name || references.contains info.name then
          env ← unsafe addConstant env info
    let mut signatures := {}
    for name in names do
      let info? := parts.findSome? fun (moduleData, _) =>
        moduleData.constants.find? (·.name == name)
      let signature ← match info? with
        | some info =>
          try unsafe render env info
          catch _ => pure (unavailable name)
        | none => pure (unavailable name)
      signatures := signatures.insert name signature
    return (signatures, regions)
  catch _ =>
    let mut signatures := {}
    for name in names do
      signatures := signatures.insert name (unavailable name)
    return (signatures, regions)

/--
Render selected exported constants from one `.olean` without importing its dependency environment.
The returned names and strings do not retain references into the mapped module data.
-/
unsafe def load (moduleName : Name) (names : NameSet)
    (moduleOf? : Name → Option Name) : IO (NameMap String) := do
  try
    let path ← findOLean moduleName
    let targetPart ← readModuleData path
    let references := referencedConstants targetPart.1 names
    let mut supportModules : NameSet := {}
    for name in references do
      if let some supportModule := moduleOf? name then
        if supportModule != moduleName then
          supportModules := supportModules.insert supportModule
    let mut parts := #[targetPart]
    for supportModule in supportModules do
      try
        parts := parts.push (← readModuleData (← findOLean supportModule))
      catch _ =>
        pure ()
    let (signatures, regions) ← unsafe renderParts parts names references
    for region in regions do
      unsafe region.free
    return signatures
  catch _ =>
    return {}

end LeanReach.Signatures
