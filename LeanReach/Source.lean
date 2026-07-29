import Lean.Server.References

namespace LeanReach

open Lean

def loadIlean? (olean : System.FilePath) : IO (Option Server.Ilean) := do
  let path := olean.withExtension "ilean"
  unless ← path.pathExists do return none
  return some (← Server.Ilean.load path)

def sourcePositions (olean : System.FilePath) : IO (NameMap (Nat × Nat)) := do
  let some ilean ← loadIlean? olean | return {}
  let mut positions := ilean.decls.foldl (init := {}) fun positions name info =>
    let position := info.selectionRange.start
    positions.insert name.toName (position.line + 1, position.character + 1)
  for (ident, info) in ilean.references do
    if let some location := info.definition? then
      if let .const _ name := ident then
        let position := location.range.start
        positions := positions.insert name.toName
          (position.line + 1, position.character + 1)
  return positions

end LeanReach
