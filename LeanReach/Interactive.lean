import LeanReach.Options
import LeanReach.Output
import LeanReach.SourceIndex

namespace LeanReach

open Lean

namespace Interactive

inductive Command where
  | query
  | search
  deriving FromJson

structure Request where
  command : Command
  query : String
  direction? : Option Direction := none
  depth? : Option Nat := none
  limit? : Option Nat := none
  deriving FromJson

private def Command.label : Command → String
  | .query => "query"
  | .search => "search"

private def decode (defaults : QueryOptions) (line : String) :
    Except String (Request × QueryOptions) := do
  let request : Request ← fromJson? (← Json.parse line)
  let query := request.query.trimAscii.copy
  if query.isEmpty then
    throw "field 'query' must be non-empty"
  let depth ← validateDepth "field 'depth'" (request.depth?.getD defaults.depth)
  let limit ← validateLimit "field 'limit'" (request.limit?.getD defaults.limit)
  return (
    { request with query },
    { defaults with
      direction := request.direction?.getD defaults.direction
      depth
      limit }
  )

private def failure (message : String) : Json :=
  toJson ({ error := message } : QueryFailure)

private def process (index : SourceIndex.Index) (sourcePath : SearchPath)
    (request : Request) (options : QueryOptions) : IO Json := do
  match request.command with
  | .query =>
    return match ← SourceIndex.runQuery index sourcePath request.query options with
      | .ok result => toJson result
      | .error error => toJson error
  | .search =>
    return toJson (← SourceIndex.runSearch index sourcePath request.query options)

private def reportProfile (enabled : Bool) (command : String) (started : Nat) : IO Unit := do
  if enabled then
    IO.eprintln
      s!"leanreach request: command={command} elapsed={(← IO.monoMsNow) - started}ms"

/-- Run the NDJSON protocol against one mapped source index until stdin reaches EOF. -/
def run (index : SourceIndex.Index) (sourcePath : SearchPath)
    (defaults : QueryOptions) (profile : Bool := false) : IO UInt32 := do
  let stdin ← IO.getStdin
  while true do
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAscii.copy
    unless line.isEmpty do
      let started ← IO.monoMsNow
      match decode defaults line with
      | .error message =>
        printJsonLine <| failure s!"invalid request: {message}"
        reportProfile profile "invalid" started
      | .ok (request, options) =>
        try
          printJsonLine (← process index sourcePath request options)
          reportProfile profile request.command.label started
        catch error =>
          printJsonLine <| failure s!"request failed: {error}"
          reportProfile profile "error" started
  return 0

end Interactive

end LeanReach
