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

private unsafe def process (session : SourceIndex.Session)
    (request : Request) (options : QueryOptions) : IO Json := do
  match request.command with
  | .query =>
    return match ← SourceIndex.runQuery session request.query options with
      | .ok result => toJson result
      | .error error => toJson error
  | .search =>
    return toJson (← SourceIndex.runSearch session request.query options)

private def reportProfile (enabled : Bool) (command : String) (started : Nat) : IO Unit := do
  if enabled then
    IO.eprintln
      s!"leanreach request: command={command} elapsed={(← IO.monoMsNow) - started}ms"

/-- Run the NDJSON protocol against one mapped source index until stdin reaches EOF. -/
unsafe def run (session : SourceIndex.Session)
    (defaults : QueryOptions) (profile : Bool := false) : IO UInt32 := do
  let stdin ← IO.getStdin
  while true do
    let line ← stdin.getLine
    if line.isEmpty then break
    unless line.trimAscii.isEmpty do
      let started ← if profile then IO.monoMsNow else pure 0
      let (response, command) ← match decode defaults line with
      | .error message =>
        pure (failure s!"invalid request: {message}", "invalid")
      | .ok (request, options) =>
        try
          let response ← unsafe process session request options
          pure (response, request.command.label)
        catch error =>
          pure (failure s!"request failed: {error}", "error")
      printJsonLine response
      reportProfile profile command started
  return 0

end Interactive

end LeanReach
