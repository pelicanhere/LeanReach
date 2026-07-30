import Lean.Environment
import Lean.Util.Path

namespace LeanReach.ModuleData

open Lean

unsafe def readParts (olean : System.FilePath) :
    IO (Array (ModuleData × CompactedRegion) × Nat) := do
  let mut paths := #[olean]
  let mut visible := 0
  let server := OLeanLevel.server.adjustFileName olean
  if ← server.pathExists then
    paths := paths.push server
    visible := paths.size - 1
  let privatePath := OLeanLevel.private.adjustFileName olean
  if ← privatePath.pathExists then paths := paths.push privatePath
  return (← readModuleDataParts paths, visible)

private def privateModule? (name : Name) : Option Name :=
  match privatePrefix? name with
  | some (.num p 0) => some (p.replacePrefix privateHeader .anonymous)
  | _ => none

private unsafe def addConstant (env : Environment) (privateNames : NameHashSet)
    (info : ConstantInfo) : IO (Environment × NameHashSet) := do
  if env.contains info.name then return (env, privateNames)
  let isPrivate := isPrivateName info.name
  let userName := privateToUserName info.name
  if isPrivate && privateNames.contains userName then return (env, privateNames)
  let added ← env.addConstAsync info.name (.ofConstantInfo info)
    (exportedKind? := none) (reportExts := false) (checkMayContain := false)
  added.commitConst added.asyncEnv (some info)
  return (added.mainEnv, if isPrivate then privateNames.insert userName else privateNames)

unsafe def withPrivateOverlay {α : Type} (env : Environment) (moduleName : Name)
    (signatureNames bodyNames : Array Name) (moduleOf? : Name → Option Name)
    (action : Environment → IO α) : IO (α × Nat) := do
  let started ← IO.monoNanosNow
  let ((result, overlayNanos), regions) ←
      show IO ((α × Nat) × Array CompactedRegion) from do
    let (parts, _) ← unsafe readParts (← findOLean moduleName)
    let some (data, _) := parts.back? |
      throw <| IO.userError s!"empty module data for '{moduleName}'"
    let mut regions := parts.map (·.2)
    let mut modules : NameMap ModuleData := {}
    modules := modules.insert moduleName data
    let mut env := env
    let mut privateNames : NameHashSet := {}
    let mut pending :=
      signatureNames.map (·, moduleName, false) ++
      bodyNames.map (·, moduleName, true)
    let mut seen : NameHashSet := {}
    while let some (name, owner, scanValue) := pending.back? do
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      let data ← match modules.find? owner with
        | some data => pure data
        | none => do
          let (parts, _) ← unsafe readParts (← findOLean owner)
          let some (data, _) := parts.back? |
            throw <| IO.userError s!"empty module data for '{owner}'"
          regions := regions ++ parts.map (·.2)
          modules := modules.insert owner data
          pure data
      let some info := data.constants.find? (·.name == name) | continue
      (env, privateNames) ← unsafe addConstant env privateNames info
      let dependencies :=
        if scanValue then info.getUsedConstantsAsSet
        else info.type.getUsedConstantsAsSet
      for dependency in dependencies do
        unless env.contains dependency || seen.contains dependency do
          let owner? :=
            if data.constants.any (·.name == dependency) then some owner
            else
              privateModule? dependency <|>
                (env.getModuleIdxFor? dependency >>= fun index =>
                  env.header.moduleNames[index.toNat]?) <|>
                moduleOf? dependency
          if let some owner := owner? then pending := pending.push (dependency, owner, false)
    let overlayNanos := (← IO.monoNanosNow) - started
    return ((← action env, overlayNanos), regions)
  regions.forM CompactedRegion.free
  return (result, overlayNanos)

end LeanReach.ModuleData
