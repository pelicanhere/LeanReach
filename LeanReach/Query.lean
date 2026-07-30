import LeanReach.PrettyPrint.Declaration
import LeanReach.Search.Index

namespace LeanReach

open Lean Meta

abbrev QueryResult := Neighborhood Declaration

instance : ToJson QueryResult where
  toJson result := Json.mkObj [
    ("target", toJson result.target),
    ("upstream", toJson result.upstream),
    ("downstream", toJson result.downstream)
  ]

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
  let some declaration := (← session.declarations.get).find? name |
    throwError "declaration '{name}' was not prepared"
  return declaration

abbrev QueryNames := Neighborhood Name

def CachedQuery.queryNames (query : CachedQuery) (limits : Limits) : QueryNames :=
  {
    target := query.target.name
    upstream := (query.upstream.take limits.upstream).map (·.name)
    downstream := (query.downstream.take limits.downstream).map (·.name)
  }

def CachedQuery.moduleOf? (query : CachedQuery) (name : Name) : Option Name :=
  if query.target.name == name then some query.target.moduleName
  else
    (query.upstream ++ query.downstream).find? (·.name == name) |>.map (·.moduleName)

def Index.queryNames (index : Index) (query : String) (limits : Limits := {}) :
    Except String QueryNames := do
  let target ← index.resolve query
  return {
    target
    upstream := index.upstream target limits.upstream
    downstream := index.downstream target limits.downstream
  }

def Session.describeNames (session : Session) (items : Array Name) :
    CoreM (Array Declaration) :=
  items.mapM (describe session)

def Session.describeQuery (session : Session) (names : QueryNames) :
    CoreM QueryResult := do
  return {
    target := ← describe session names.target
    upstream := ← session.describeNames names.upstream
    downstream := ← session.describeNames names.downstream
  }

end LeanReach
