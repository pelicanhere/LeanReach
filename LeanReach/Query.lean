import LeanReach.Index
import LeanReach.PrettyPrint

namespace LeanReach

open Lean Meta

structure QueryResult where
  target : Declaration
  upstream : Array Declaration
  downstream : Array Declaration
  deriving ToJson

structure Limits where
  upstream : Nat := 10
  downstream : Nat := 10
  search : Nat := 20

def Limits.uniform (limit : Nat) : Limits :=
  { upstream := limit, downstream := limit, search := limit }

structure Session where
  private index : Index
  private sourcePath : SearchPath
  private bundle : Array Declaration
  private declarations : IO.Ref (NameMap Declaration)

def Session.create (index : Index) (sourcePath : SearchPath)
    (bundle : Array Declaration := #[]) : IO Session :=
  return { index, sourcePath, bundle, declarations := ← IO.mkRef {} }

def Session.ppCache (session : Session) : IO (NameMap Declaration) :=
  session.declarations.get

def Session.merge (session : Session) (declarations : NameMap Declaration) : IO Unit := do
  session.declarations.modify fun current => Id.run do
    let mut current := current
    for (name, declaration) in declarations do
      current := current.insert name declaration
    return current

private def Session.bundled? (session : Session) (name : Name) : Option Declaration :=
  (session.index.idOf? name).bind (session.bundle[·.toNat]?)

def Session.missing (session : Session) (names : Array Name) : IO (Array Name) := do
  let cached ← session.declarations.get
  return names.filter fun name =>
    !cached.contains name && (session.bundled? name).isNone

private def describe (session : Session) (name : Name) : CoreM Declaration := do
  if let some declaration := (← session.declarations.get).find? name then
    return declaration
  if let some declaration := session.bundled? name then
    return declaration
  let declaration ← prettyPrintDeclaration session.sourcePath name
  session.declarations.modify (·.insert name declaration)
  return declaration

abbrev QueryNames := Name × Array Name × Array Name

def QueryNames.all (names : QueryNames) : Array Name :=
  #[names.1] ++ names.2.1 ++ names.2.2

def Index.queryNames (index : Index) (query : String) (limits : Limits := {}) :
    Except String QueryNames := do
  let target ← index.resolve query
  return (
    target,
    index.upstream target limits.upstream,
    index.downstream target limits.downstream
  )

def Session.describeNames (session : Session) (items : Array Name) :
    CoreM (Array Declaration) :=
  items.mapM (describe session)

private def liftQuery {α : Type} : Except String α → CoreM α
  | .ok result => pure result
  | .error message => throwError message

def Session.describeQuery (session : Session) (names : QueryNames) :
    CoreM QueryResult := do
  let (target, upstream, downstream) := names
  return {
    target := ← describe session target
    upstream := ← session.describeNames upstream
    downstream := ← session.describeNames downstream
  }

def Session.query (session : Session) (query : String) (limits : Limits := {}) :
    CoreM QueryResult := do
  session.describeQuery (← liftQuery (session.index.queryNames query limits))

def Session.search (session : Session) (query : String) (limit : Nat := 20) :
    CoreM (Array Declaration) :=
  session.describeNames (session.index.search query limit)

def Session.cacheNames (session : Session) (names : Array Name) : CoreM Nat := do
  names.forM fun name =>
    try discard <| describe session name
    catch error => throwError "failed to cache '{name}': {error.toMessageData}"
  return names.size

end LeanReach
