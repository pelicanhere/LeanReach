import Lean.DeclarationRange
import Lean.PrettyPrinter.Delaborator.Builtins
import Lean.Structure
import Lean.Util.Path
import LeanReach.Declaration
import LeanReach.Index

namespace LeanReach

open Lean Meta

structure QueryResult where
  target : Declaration
  upstream : Array Declaration
  downstream : Array Declaration
  deriving ToJson

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
  try
    let expression ← mkConstWithLevelParams name
    let (stx, _) ← PrettyPrinter.delabCore expression
      (delab := PrettyPrinter.Delaborator.delabConstWithSignature (universes := false))
    return (← PrettyPrinter.ppTerm ⟨stx⟩).pretty (width := 10000)
  catch _ =>
    let info ← getConstInfo name
    return s!"{name} : {(← PrettyPrinter.ppExpr info.type).pretty (width := 10000)}"

private def renderList (label : String) (names : Array Name) : MetaM String := do
  if names.isEmpty then return ""
  let lines ← names.mapM renderSignature
  return s!"\n  {label}:\n    {String.intercalate "\n    " lines.toList}"

private def renderDeclaration (name : Name) (info : ConstantInfo) : MetaM String :=
    withCurrHeartbeats do
  let signature ← renderSignature name
  if info.isTheorem || (← isProp info.type) then return signature
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

abbrev QueryNames := Name × Array Name × Array Name

def Index.queryNames (index : Index) (query : String) (upstreamLimit : Nat := 6)
    (downstreamLimit : Nat := 10) : Except String QueryNames := do
  let target ← index.resolve query
  return (
    target,
    index.upstream target upstreamLimit,
    index.downstream target downstreamLimit
  )

private def describeRelated (session : Session) (items : Array Name) :
    CoreM (Array Declaration) :=
  items.mapM (describe session)

private def liftQuery {α : Type} : Except String α → CoreM α
  | .ok result => pure result
  | .error message => throwError message

def Session.query (session : Session) (query : String) (upstreamLimit : Nat := 6)
    (downstreamLimit : Nat := 10) : CoreM QueryResult := do
  let (target, upstream, downstream) ←
    liftQuery (session.index.queryNames query upstreamLimit downstreamLimit)
  return {
    target := ← describe session target
    upstream := ← describeRelated session upstream
    downstream := ← describeRelated session downstream
  }

def Session.search (session : Session) (query : String) (limit : Nat := 20) :
    CoreM (Array Declaration) :=
  (session.index.search query limit).mapM (describe session)

def Session.cacheNames (session : Session) (names : Array Name) : CoreM Nat := do
  names.forM fun name =>
    try discard <| describe session name
    catch error => throwError "failed to cache '{name}': {error.toMessageData}"
  return names.size

def Session.cacheModules (session : Session) (modules : Array Name) : CoreM Nat :=
  session.cacheNames (session.index.namesInModules modules)

end LeanReach
