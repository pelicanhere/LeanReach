import Lean.Server.References
import Lean.Util.Path

namespace LeanReach

open Lean

private def loadIlean? (olean : System.FilePath) : IO (Option Server.Ilean) := do
  let path := olean.withExtension "ilean"
  unless ← path.pathExists do return none
  return some (← Server.Ilean.load path)

private def foldDefinitions {α : Type} (ilean : Server.Ilean) (init : α)
    (visit : α → Name → Lsp.Position → α) : α := Id.run do
  let mut result := ilean.decls.foldl (init := init) fun result name info =>
    visit result name.toName info.selectionRange.start
  for (ident, info) in ilean.references do
    if let some location := info.definition? then
      if let .const _ name := ident then
        result := visit result name.toName location.range.start
  return result

def sourceNames (olean : System.FilePath) : IO (Std.HashSet String) := do
  let some ilean ← loadIlean? olean | return {}
  return foldDefinitions ilean {} fun names name _ => names.insert name.toString

def moduleSource (sourcePath : SearchPath) (moduleName : Name) :
    IO (Option String × NameMap Lsp.Position) := do
  let olean ← findOLean moduleName
  let positions ← match ← loadIlean? olean with
    | none => pure {}
    | some ilean => pure <| foldDefinitions ilean {} fun positions name position =>
        positions.insert name position
  return ((← sourcePath.findModuleWithExt "lean" moduleName).map (·.toString), positions)

end LeanReach
