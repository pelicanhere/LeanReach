import LeanReach.Options
import LeanReach.Output
import LeanReach.SourceIndex

namespace LeanReach

open Lean

private inductive Request where
  | query (id? : Option Json) (query : String) (options : QueryOptions)
  | search (id? : Option Json) (query : String) (options : QueryOptions)
  | ping (id? : Option Json)
  | quit (id? : Option Json)

private def Request.id? : Request → Option Json
  | .query id? .. | .search id? .. | .ping id? | .quit id? => id?

private def Request.command : Request → String
  | .query .. => "query"
  | .search .. => "search"
  | .ping .. => "ping"
  | .quit .. => "quit"

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

private def optionalField {α : Type} [FromJson α] (json : Json) (name : String) :
    Except String (Option α) :=
  match json.getObjValAs? (Option α) name with
  | .ok value => .ok value
  | .error message => .error s!"field '{name}': {message}"

private def requiredQuery (json : Json) : Except String String := do
  let query? : Option String ← optionalField json "query"
  let some query := query? | throw "missing required field 'query'"
  let query := query.trimAscii.copy
  if query.isEmpty then
    throw "field 'query' must be non-empty"
  return query

private def requestOptions (defaults : QueryOptions) (json : Json) :
    Except String QueryOptions := do
  let direction? : Option String ← optionalField json "direction"
  let depth? : Option Nat ← optionalField json "depth"
  let limit? : Option Nat ← optionalField json "limit"
  let includeInternal? : Option Bool ← optionalField json "includeInternal"
  let direction ← match direction? with
    | some direction => parseDirection "field 'direction'" direction
    | none => pure defaults.direction
  let depth ← match depth? with
    | some depth => validateDepth "field 'depth'" depth
    | none => pure defaults.depth
  let limit ← match limit? with
    | some limit => validateLimit "field 'limit'" limit
    | none => pure defaults.limit
  return {
    defaults with
    direction
    depth
    limit
    includeInternal := includeInternal?.getD defaults.includeInternal
  }

private def searchOptions (defaults : QueryOptions) (json : Json) :
    Except String QueryOptions := do
  let limit? : Option Nat ← optionalField json "limit"
  let includeInternal? : Option Bool ← optionalField json "includeInternal"
  let limit ← match limit? with
    | some limit => validateLimit "field 'limit'" limit
    | none => pure defaults.limit
  return {
    defaults with
    limit
    includeInternal := includeInternal?.getD defaults.includeInternal
  }

private def attachId {α : Type} (id? : Option Json) :
    Except String α → Except (Option Json × String) α
  | .ok value => .ok value
  | .error message => .error (id?, message)

private def requestId : Json → Option Json
  | .obj fields =>
    match fields.get? "id" with
    | some .null | none => none
    | some id => some id
  | _ => none

private def decodeRequest (defaults : QueryOptions) (line : String) :
    Except (Option Json × String) Request := do
  let json ← match Json.parse line with
    | .ok json => pure json
    | .error message => throw (none, message)
  let .obj _ := json | throw (none, "object expected")
  let id? := requestId json
  let command? : Option String ← attachId id? (optionalField json "command")
  match command?.getD "query" with
  | "query" =>
    return .query id?
      (← attachId id? (requiredQuery json))
      (← attachId id? (requestOptions defaults json))
  | "search" =>
    return .search id?
      (← attachId id? (requiredQuery json))
      (← attachId id? (searchOptions defaults json))
  | "ping" => return .ping id?
  | "quit" => return .quit id?
  | command =>
    throw (id?, s!"unknown command '{command}'; expected query, search, ping, or quit")

private def processRequest (index : SourceIndex.Index) (sourcePath : SearchPath)
    (request : Request) :
    IO (Json × Bool) := do
  match request with
  | .query id? query options =>
    match ← SourceIndex.runQuery index sourcePath query options with
    | .ok result =>
      return (successResponse id? (toJson result), true)
    | .error failure =>
      return (errorResponse id? failure.error (some failure.candidates), true)
  | .search id? query options =>
    let result ← SourceIndex.runSearch index sourcePath query options
    return (successResponse id? (toJson result), true)
  | .ping id? =>
    return (
      successResponse id? <| Json.mkObj [
        ("status", toJson "ready")
      ],
      true
    )
  | .quit id? =>
    return (
      successResponse id? <| Json.mkObj [("status", toJson "bye")],
      false
    )

private partial def serve (defaults : QueryOptions) (profile : Bool)
    (process : Request → IO (Json × Bool)) : IO UInt32 := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then
    return 0
  let line := line.trimAscii.copy
  if line.isEmpty then
    serve defaults profile process
  else
    let started ← IO.monoMsNow
    match decodeRequest defaults line with
    | .error (id?, message) =>
      printJsonLine <| errorResponse id? s!"invalid request: {message}"
      if profile then
        let finished ← IO.monoMsNow
        IO.eprintln s!"leanreach request: command=invalid elapsed={finished - started}ms"
      serve defaults profile process
    | .ok request =>
      try
        let (response, keepRunning) ← process request
        printJsonLine response
        if profile then
          let finished ← IO.monoMsNow
          IO.eprintln
            s!"leanreach request: command={request.command} elapsed={finished - started}ms"
        if keepRunning then
          serve defaults profile process
        else
          return 0
      catch error =>
        printJsonLine <| errorResponse request.id? s!"request failed: {error}"
        if profile then
          let finished ← IO.monoMsNow
          IO.eprintln s!"leanreach request: command=error elapsed={finished - started}ms"
        serve defaults profile process

/-- Run the NDJSON protocol against one mapped source index. -/
def runIndexedInteractive (index : SourceIndex.Index) (sourcePath : SearchPath)
    (defaults : QueryOptions) (profile : Bool := false) : IO UInt32 :=
  serve defaults profile (processRequest index sourcePath)

end LeanReach
