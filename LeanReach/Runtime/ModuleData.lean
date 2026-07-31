import Lean.Environment

namespace LeanReach.ModuleData

open Lean

unsafe def readParts (olean : System.FilePath) :
    IO (Array (ModuleData × CompactedRegion)) := do
  let additional ← #[OLeanLevel.server, OLeanLevel.private].map
    (·.adjustFileName olean) |>.filterM (·.pathExists)
  readModuleDataParts (#[olean] ++ additional)

private def privateModule? (name : Name) : Option Name :=
  match privatePrefix? name with
  | some (.num p 0) => some (p.replacePrefix privateHeader .anonymous)
  | _ => none

private unsafe def addConstant (env : Environment) (info : ConstantInfo) : IO Environment := do
  if env.contains info.name then return env
  let added ← env.addConstAsync info.name (.ofConstantInfo info)
    (exportedKind? := none) (reportExts := false) (checkMayContain := false)
  added.commitConst added.asyncEnv (some info)
  return added.mainEnv

private def constantMap (data : ModuleData) : NameMap ConstantInfo :=
  data.constants.foldl (init := {}) fun result info => result.insert info.name info

unsafe def withPrivateOverlay {α : Type} (env : Environment) (moduleName : Name)
    (signatureNames bodyNames : Array Name) (moduleOf? : Name → Option Name)
    (action : Environment → IO α) : IO (α × Nat) := do
  let started ← IO.monoNanosNow
  let mut regions : Array CompactedRegion := #[]
  try
    let parts ← unsafe readParts (← findOLean moduleName)
    regions := parts.map (·.2)
    let some (data, _) := parts.back? |
      throw <| IO.userError s!"empty module data for '{moduleName}'"
    let mut modules : NameMap (NameMap ConstantInfo) := {}
    modules := modules.insert moduleName (constantMap data)
    let mut env := env
    let mut pending :=
      signatureNames.map (·, moduleName, false) ++
      bodyNames.map (·, moduleName, true)
    let mut seen : NameHashSet := {}
    while let some (name, owner, scanValue) := pending.back? do
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      let constants ← match modules.find? owner with
        | some constants => pure constants
        | none => do
          let parts ← unsafe readParts (← findOLean owner)
          for (_, region) in parts do regions := regions.push region
          let some (data, _) := parts.back? |
            throw <| IO.userError s!"empty module data for '{owner}'"
          let result := constantMap data
          modules := modules.insert owner result
          pure result
      let some info := constants.find? name | continue
      env ← unsafe addConstant env info
      let dependencies :=
        if scanValue then info.getUsedConstantsAsSet
        else info.type.getUsedConstantsAsSet
      for dependency in dependencies do
        unless env.contains dependency || seen.contains dependency do
          let owner? :=
            if constants.contains dependency then some owner
            else
              privateModule? dependency <|>
                (env.getModuleIdxFor? dependency >>= fun index =>
                  env.header.moduleNames[index.toNat]?) <|>
                moduleOf? dependency
          if let some owner := owner? then pending := pending.push (dependency, owner, false)
    let overlayNanos := (← IO.monoNanosNow) - started
    return (← action env, overlayNanos)
  finally
    regions.forM CompactedRegion.free

end LeanReach.ModuleData
