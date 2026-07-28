import Lean.DeclarationRange
import Lean.PrettyPrinter.Delaborator.Builtins
import Lean.Structure
import Lean.Util.Path
import LeanReach.Declaration
import LeanReach.Rank

namespace LeanReach

open Lean Meta

abbrev Related := Nat × Declaration

structure QueryResult where
  target : Declaration
  upstream : Array Related
  downstream : Array Related

private def relatedJson : Related → Json
  | (distance, declaration) => Json.mkObj [
      ("distance", toJson distance), ("declaration", toJson declaration)
    ]

instance : ToJson QueryResult where
  toJson result := Json.mkObj [
    ("target", toJson result.target),
    ("upstream", Json.arr <| result.upstream.map relatedJson),
    ("downstream", Json.arr <| result.downstream.map relatedJson)
  ]

structure RankedDeclaration where
  score : Float
  distance : Nat
  documentFrequency : Nat
  declaration : Declaration
  deriving ToJson

structure QueryOptions where
  depth : Nat := 1
  limit : Nat := 20
  upstream : Bool := true
  downstream : Bool := true

structure Session where
  private index : Index
  private sourcePath : SearchPath
  private declarations : IO.Ref (NameMap Declaration)

def Session.create (index : Index) (sourcePath : SearchPath)
    (declarations : NameMap Declaration := {}) : IO Session :=
  return { index, sourcePath, declarations := ← IO.mkRef declarations }

def Session.rendered (session : Session) : IO (NameMap Declaration) :=
  session.declarations.get

private def renderSignature (name : Name) : MetaM String := do
  let expression ← mkConstWithLevelParams name
  let (stx, _) ← PrettyPrinter.delabCore expression
    (delab := PrettyPrinter.Delaborator.delabConstWithSignature (universes := false))
  return (← PrettyPrinter.ppTerm ⟨stx⟩).pretty (width := 10000)

private def renderList (label : String) (names : Array Name) : MetaM String := do
  if names.isEmpty then return ""
  let lines ← names.mapM renderSignature
  return s!"\n  {label}:\n    {String.intercalate "\n    " lines.toList}"

private def renderDeclaration (name : Name) (info : ConstantInfo) : MetaM String :=
    withCurrHeartbeats do
  let signature ← renderSignature name
  if ← isProp info.type then return signature
  if let some value := info.value? (allowOpaque := true) then
    let body := (← PrettyPrinter.ppExpr value).pretty (width := 100)
    return s!"{signature} :=\n  {body.replace "\n" "\n  "}"
  let .inductInfo inductiveInfo := info | return signature
  let env ← getEnv
  let fields :=
    if isStructure env name then
      getStructureFieldsFlattened env name (includeSubobjectFields := false)
        |>.filterMap (getProjFnForField? env name)
    else #[]
  return signature ++
    (← renderList "fields" fields) ++
    (← renderList "constructors" inductiveInfo.ctors.toArray)

private def describe (session : Session) (name : Name) : CoreM Declaration := do
  if let some declaration := (← session.declarations.get).find? name then
    return declaration
  let env ← getEnv
  let some info := env.find? name | throwError "unknown declaration '{name}'"
  let moduleName? ← findModuleOf? name
  let file? ← moduleName?.mapM fun moduleName =>
    return (← session.sourcePath.findModuleWithExt "lean" moduleName).map (·.toString)
  let range? := (← findDeclarationRanges? name).map (·.selectionRange)
  let declaration := {
    name := name.toString
    signature := ← MetaM.run' (renderDeclaration name info)
    moduleName := moduleName?.map (·.toString) |>.getD ""
    file := file?.getD none
    line := range?.map (·.pos.line) |>.getD 0
    column := range?.map (·.pos.column + 1) |>.getD 0
  }
  session.declarations.modify (·.insert name declaration)
  return declaration

private def traverse (start : Name) (depth limit : Nat)
    (neighbors : Name → Array Name) : Array (Nat × Name) := Id.run do
  if depth == 0 || limit == 0 then return #[]
  let mut visited : NameHashSet := ({} : NameHashSet).insert start
  let mut frontier := #[start]
  let mut found := #[]
  for distance in [1:depth + 1] do
    let mut next := #[]
    for name in frontier do
      for neighbor in neighbors name do
        unless visited.contains neighbor do
          visited := visited.insert neighbor
          next := next.push neighbor
          found := found.push (distance, neighbor)
          if found.size == limit then return found
    frontier := next
    if frontier.isEmpty then break
  return found

abbrev QueryNames := Name × Array (Nat × Name) × Array (Nat × Name)

def Index.queryNames (index : Index) (query : String) (options : QueryOptions := {}) :
    Except String QueryNames := do
  let target ← index.resolve query
  return (
    target,
    if options.upstream then
      traverse target options.depth options.limit index.upstream
    else #[],
    if options.downstream then
      traverse target options.depth options.limit index.downstream
    else #[]
  )

private def describeRelated (session : Session) (items : Array (Nat × Name)) :
    CoreM (Array Related) :=
  items.mapM fun (distance, name) => return (distance, ← describe session name)

private def liftQuery {α : Type} : Except String α → CoreM α
  | .ok result => pure result
  | .error message => throwError message

def Session.query (session : Session) (query : String) (options : QueryOptions := {}) :
    CoreM QueryResult := do
  let (target, upstream, downstream) ←
    liftQuery (session.index.queryNames query options)
  return {
    target := ← describe session target
    upstream := ← describeRelated session upstream
    downstream := ← describeRelated session downstream
  }

def Session.search (session : Session) (query : String) (limit : Nat := 20) :
    CoreM (Array Declaration) :=
  (session.index.search query limit).mapM (describe session)

def Session.context (session : Session) (query : String) (depth : Nat := 1)
    (limit : Nat := 20) : CoreM (Declaration × Array RankedDeclaration) := do
  let (target, names) ←
    liftQuery (session.index.contextNames query depth limit)
  let items ← names.mapM fun (score, distance, name) =>
    return {
      score
      distance
      documentFrequency := session.index.documentFrequency name
      declaration := ← describe session name
    }
  return (← describe session target, items)

end LeanReach
