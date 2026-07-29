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

def Limits.usesCachedQuery (limits : Limits) : Bool :=
  limits.upstream ≤ cachedQueryLimit && limits.downstream ≤ cachedQueryLimit

structure Session where
  sourcePath : SearchPath
  private declarations : IO.Ref (NameMap Declaration)

def Session.create (sourcePath : SearchPath) : IO Session :=
  return { sourcePath, declarations := ← IO.mkRef {} }

def Session.ppCache (session : Session) : IO (NameMap Declaration) :=
  session.declarations.get

def Session.merge (session : Session) (declarations : NameMap Declaration) : IO Unit := do
  session.declarations.modify fun current => Std.TreeMap.union current declarations

def Session.missing (session : Session) (names : Array Name) : IO (Array Name) := do
  let cached ← session.declarations.get
  return names.filter fun name => !cached.contains name

private def describe (session : Session) (name : Name) : CoreM Declaration := do
  if let some declaration := (← session.declarations.get).find? name then
    return declaration
  let declaration ← prettyPrintDeclaration session.sourcePath name
  session.declarations.modify (·.insert name declaration)
  return declaration

abbrev QueryNames := Name × Array Name × Array Name

def QueryNames.all (names : QueryNames) : Array Name :=
  #[names.1] ++ names.2.1 ++ names.2.2

def CachedQuery.queryNames (query : CachedQuery) (limits : Limits) : QueryNames :=
  (
    query.target.name,
    (query.upstream.take limits.upstream).map (·.name),
    (query.downstream.take limits.downstream).map (·.name)
  )

def CachedQuery.moduleOf? (query : CachedQuery) (name : Name) : Option Name :=
  if query.target.name == name then some query.target.moduleName
  else
    (query.upstream ++ query.downstream).find? (·.name == name) |>.map (·.moduleName)

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

def Session.query (session : Session) (index : Index) (query : String)
    (limits : Limits := {}) :
    CoreM QueryResult := do
  session.describeQuery (← liftQuery (index.queryNames query limits))

def Session.search (session : Session) (index : Index) (query : String)
    (limit : Nat := 20) :
    CoreM (Array Declaration) :=
  session.describeNames (index.search query limit)

end LeanReach
