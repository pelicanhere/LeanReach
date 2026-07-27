import LeanReach.Protocol

namespace LeanReach

open Lean

private def formatLocation (source : SourceLocation) : String :=
  match source.file with
  | some file => s!"{file}:{source.line}:{source.column}"
  | none => s!"{source.moduleName}:{source.line}:{source.column}"

private def printDeclaration (indent : String) (declaration : DeclarationView) : IO Unit := do
  IO.println s!"{indent}{declaration.name}"
  IO.println s!"{indent}  {formatLocation declaration.source}"

private def printRelations (label : String) (relations : RelationList) : IO Unit := do
  IO.println s!"{label} ({relations.total})"
  if relations.items.isEmpty then
    IO.println "  <none>"
  for relation in relations.items do
    let via := (relation.via.map fun name => s!" via {name}").getD ""
    IO.println s!"  d={relation.distance} {relation.declaration.name}{via}"
    IO.println s!"      {formatLocation relation.declaration.source}"
  if relations.items.size < relations.total then
    IO.println s!"  ... {relations.total - relations.items.size} more (increase --limit)"

def printQueryHuman (result : QueryResult) : IO Unit := do
  printDeclaration "target  " result.target
  printRelations "upstream" result.upstream
  printRelations "downstream" result.downstream

def printFailureHuman (failure : QueryFailure) : IO Unit := do
  IO.eprintln s!"leanreach: {failure.error}"
  unless failure.candidates.isEmpty do
    IO.eprintln "candidates:"
    for declaration in failure.candidates do
      IO.eprintln s!"  {declaration.name}  {formatLocation declaration.source}"

def printSearchHuman (result : SearchResult) : IO Unit := do
  IO.println s!"matches ({result.total})"
  if result.items.isEmpty then
    IO.println "  <none>"
  for declaration in result.items do
    printDeclaration "  " declaration
  if result.items.size < result.total then
    IO.println s!"  ... {result.total - result.items.size} more (increase --limit)"

def printJson {α : Type} [ToJson α] (value : α) : IO Unit :=
  IO.println (toJson value).pretty

/-- Emit exactly one compact JSON value and flush it for long-lived pipe clients. -/
def printJsonLine (value : Json) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr (value.compress ++ "\n")
  stdout.flush

end LeanReach
