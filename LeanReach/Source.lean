import Lean.Server.References

namespace LeanReach

open Lean

def loadIlean? (olean : System.FilePath) : IO (Option Server.Ilean) := do
  let path := olean.withExtension "ilean"
  unless ← path.pathExists do return none
  return some (← Server.Ilean.load path)

end LeanReach
