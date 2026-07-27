import Lean.Util.FoldConsts
import LeanReach.Query.Context

namespace LeanReach.Query

open Lean

def collectKernelUpstream (env : Environment) (target : Name)
    (options : QueryOptions) : Array RawRelation := Id.run do
  let mut visited : NameSet := ({} : NameSet).insert target
  let mut frontier := #[target]
  let mut results := #[]
  for distance in [1:options.depth + 1] do
    let mut next := #[]
    for parent in frontier do
      if let some info := env.find? parent then
        for dependency in info.getUsedConstantsAsSet do
          if !visited.contains dependency then
            visited := visited.insert dependency
            next := next.push dependency
            if visibleName options.includeInternal dependency then
              results := results.push {
                declaration := dependency
                distance
                via := if distance == 1 then none else some parent
              }
    frontier := next
    if frontier.isEmpty then
      break
  return results.qsort rawRelationLt

private def firstUsedConstant (targets : NameSet) (expr : Expr) : Option Name :=
  expr.foldConsts none fun name found =>
    match found with
    | some _ => found
    | none => if targets.contains name then some name else none

private def firstUsedName (targets : NameSet) : List Name → Option Name
  | [] => none
  | name :: names =>
    if targets.contains name then some name else firstUsedName targets names

/--
Returns one direct dependency in `targets`, if present. This avoids materializing a dependency
set for every declaration during a reverse scan.
-/
private def firstDependencyIn (targets : NameSet) (info : ConstantInfo) : Option Name :=
  match firstUsedConstant targets info.type with
  | some name => some name
  | none =>
    match info.value? (allowOpaque := true) with
    | some value => firstUsedConstant targets value
    | none =>
      match info with
      | .inductInfo value => firstUsedName targets value.ctors
      | .ctorInfo value =>
        if targets.contains value.name then some value.name else none
      | .recInfo value => firstUsedName targets value.all
      | _ => none

/--
Collect downstream declarations without retaining a global reverse adjacency map. Each requested
layer is one linear environment scan; the default depth of one therefore has bounded auxiliary
memory and a single scan.
-/
def collectKernelDownstream (env : Environment) (target : Name)
    (options : QueryOptions) : Array RawRelation := Id.run do
  let mut visited : NameSet := ({} : NameSet).insert target
  let mut frontier : NameSet := ({} : NameSet).insert target
  let mut results := #[]
  for distance in [1:options.depth + 1] do
    let mut next : NameSet := {}
    for (name, info) in env.constants do
      if !visited.contains name then
        if let some via := firstDependencyIn frontier info then
          visited := visited.insert name
          next := next.insert name
          if visibleName options.includeInternal name then
            results := results.push {
              declaration := name
              distance
              via := if distance == 1 then none else some via
            }
    frontier := next
    if frontier.isEmpty then
      break
  return results.qsort rawRelationLt

end LeanReach.Query
