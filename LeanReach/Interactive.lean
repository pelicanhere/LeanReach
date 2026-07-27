import LeanReach.Options
import LeanReach.Output

namespace LeanReach

open Lean Lean.Core

private structure InteractiveRequest where
  id? : Option Json := none
  command? : Option String := none
  query? : Option String := none
  direction? : Option String := none
  depth? : Option Nat := none
  limit? : Option Nat := none
  includeInternal? : Option Bool := none
  deriving FromJson

private def responseId (id? : Option Json) : Json :=
  id?.getD Json.null

private def successResponse (id? : Option Json) (result : Json) : Json :=
  Json.mkObj [
    ("id", responseId id?),
    ("ok", toJson true),
    ("result", result)
  ]

private def errorResponse (id? : Option Json) (message : String)
    (candidates : Option (Array DeclarationView) := none) : Json :=
  Json.mkObj <|
    [
      ("id", responseId id?),
      ("ok", toJson false),
      ("error", toJson message)
    ] ++
    match candidates with
    | some candidates => [("candidates", toJson candidates)]
    | none => []

private def requiredQuery (request : InteractiveRequest) : Except String String := do
  let query ← match request.query? with
    | some query => pure query.trimAscii.copy
    | none => throw "missing required field 'query'"
  if query.isEmpty then
    throw "field 'query' must be non-empty"
  return query

private def queryOptions (defaults : QueryOptions) (request : InteractiveRequest) :
    Except String QueryOptions := do
  let direction ← match request.direction? with
    | some direction => parseDirection "field 'direction'" direction
    | none => pure defaults.direction
  let depth ← match request.depth? with
    | some depth => validateDepth "field 'depth'" depth
    | none => pure defaults.depth
  let limit ← match request.limit? with
    | some limit => validateLimit "field 'limit'" limit
    | none => pure defaults.limit
  return {
    mode := defaults.mode
    direction
    depth
    limit
    includeInternal := request.includeInternal?.getD defaults.includeInternal
  }

private def searchLimit (defaults : QueryOptions) (request : InteractiveRequest) :
    Except String Nat :=
  match request.limit? with
  | some limit => validateLimit "field 'limit'" limit
  | none => pure defaults.limit

private def processRequest (defaults : QueryOptions) (request : InteractiveRequest) :
    SessionM (Json × Bool × String) := do
  let command := request.command?.getD "query"
  match command with
  | "query" =>
    match requiredQuery request, queryOptions defaults request with
    | .error message, _ | _, .error message =>
      return (errorResponse request.id? message, true, command)
    | .ok query, .ok options =>
      match ← runQueryM query options with
      | .ok result =>
        return (successResponse request.id? (toJson result), true, command)
      | .error failure =>
        return (
          errorResponse request.id? failure.error (some failure.candidates),
          true,
          command
        )
  | "search" =>
    match requiredQuery request, searchLimit defaults request with
    | .error message, _ | _, .error message =>
      return (errorResponse request.id? message, true, command)
    | .ok query, .ok limit =>
      let result ← runSearchM query {
        defaults with
        limit
        includeInternal := request.includeInternal?.getD defaults.includeInternal
      }
      return (successResponse request.id? (toJson result), true, command)
  | "ping" =>
    return (
      successResponse request.id? <| Json.mkObj [
        ("status", toJson "ready"),
        ("mode", toJson defaults.mode.label)
      ],
      true,
      command
    )
  | "quit" =>
    return (
      successResponse request.id? <| Json.mkObj [("status", toJson "bye")],
      false,
      command
    )
  | _ =>
    return (
      errorResponse request.id?
        s!"unknown command '{command}'; expected query, search, ping, or quit",
      true,
      command
    )

private def decodeRequest (line : String) : Except String InteractiveRequest := do
  let json ← Json.parse line
  fromJson? json

/--
Run a newline-delimited JSON session. The imported environment is owned by the caller and reused
until EOF or a `quit` request.
-/
partial def runInteractive (defaults : QueryOptions) (profile : Bool := false) : CoreM UInt32 := do
  withSession do
    let stdin ← IO.getStdin
    let rec loop : SessionM UInt32 := do
      let line ← stdin.getLine
      if line.isEmpty then
        return 0
      let line := line.trimAscii.copy
      if line.isEmpty then
        loop
      else
        let started ← IO.monoMsNow
        match decodeRequest line with
        | .error message =>
          printJsonLine <| errorResponse none s!"invalid request: {message}"
          if profile then
            let finished ← IO.monoMsNow
            IO.eprintln s!"leanreach request: command=invalid elapsed={finished - started}ms"
          loop
        | .ok request =>
          try
            let (response, keepRunning, command) ← processRequest defaults request
            printJsonLine response
            if profile then
              let finished ← IO.monoMsNow
              IO.eprintln s!"leanreach request: command={command} elapsed={finished - started}ms"
            if keepRunning then loop else return 0
          catch error =>
            let message ← error.toMessageData.toString
            printJsonLine <| errorResponse request.id? s!"request failed: {message}"
            if profile then
              let finished ← IO.monoMsNow
              IO.eprintln s!"leanreach request: command=error elapsed={finished - started}ms"
            loop
    loop

end LeanReach
