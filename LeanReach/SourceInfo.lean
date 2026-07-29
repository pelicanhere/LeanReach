import Lean.Server.References
import Lean.Util.Path

namespace LeanReach

open Lean

structure SourceInfo where
  file : Option String
  positions : NameMap (Nat × Nat)

private def loadIlean? (olean : System.FilePath) : IO (Option Server.Ilean) := do
  let path := olean.withExtension "ilean"
  unless ← path.pathExists do return none
  return some (← Server.Ilean.load path)

private def foldDefinitions {α : Type} (ilean : Server.Ilean) (init : α)
    (visit : α → Name → Nat → Nat → α) : α := Id.run do
  let mut result := ilean.decls.foldl (init := init) fun result name info =>
    let position := info.selectionRange.start
    visit result name.toName position.line position.character
  for (ident, info) in ilean.references do
    if let some location := info.definition? then
      if let .const _ name := ident then
        let position := location.range.start
        result := visit result name.toName position.line position.character
  return result

def sourceNames (olean : System.FilePath) : IO (Std.HashSet String) := do
  let some ilean ← loadIlean? olean | return {}
  return foldDefinitions ilean {} fun names name _ _ => names.insert name.toString

def sourceInfo (sourcePath : SearchPath) (moduleName : Name) : IO SourceInfo := do
  let olean ← findOLean moduleName
  let positions ← match ← loadIlean? olean with
    | none => pure {}
    | some ilean => pure <| foldDefinitions ilean {} fun positions name line column =>
        positions.insert name (line + 1, column + 1)
  return {
    file := (← sourcePath.findModuleWithExt "lean" moduleName).map (·.toString)
    positions
  }

def SourceInfo.position (source : SourceInfo) (name : Name) : Nat × Nat :=
  (source.positions.find? name).getD (0, 0)

end LeanReach
