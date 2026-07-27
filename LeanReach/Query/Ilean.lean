import Lean.Server.References
import Lean.Util.Path
import LeanReach.Query.Context

namespace LeanReach.Query

open Lean

def ileanPath? (moduleName : Name) : IO (Option System.FilePath) := do
  try
    let path := (← findOLean moduleName).withExtension "ilean"
    return if ← path.pathExists then some path else none
  catch _ =>
    return none

def loadIlean? (moduleName : Name) : IO (Option Server.Ilean) := do
  let some path ← ileanPath? moduleName | return none
  return some (← Server.Ilean.load path)

def sourceDependencies (ilean : Server.Ilean) (parent : Name) : NameSet := Id.run do
  let parentName := nameString parent
  let mut dependencies : NameSet := {}
  for (ident, info) in ilean.references do
    let .const _ dependencyName := ident | continue
    if info.usages.any fun usage => usage.parentDecl? == some parentName then
      dependencies := dependencies.insert dependencyName.toName
  return dependencies

end LeanReach.Query
