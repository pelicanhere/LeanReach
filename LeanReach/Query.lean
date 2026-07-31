import LeanReach.PrettyPrint.Declaration
import LeanReach.Search.Index

namespace LeanReach

open Lean

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
  search : Nat := 10

def Limits.uniform (limit : Nat) : Limits :=
  { upstream := limit, downstream := limit, search := limit }

def Limits.usesCachedQuery (limits : Limits) : Bool :=
  limits.upstream ≤ cachedQueryLimit && limits.downstream ≤ cachedQueryLimit

structure Session where
  sourcePath : SearchPath
  private declarations : IO.Ref (NameMap Declaration)

def Session.create (sourcePath : SearchPath) : IO Session :=
  return { sourcePath, declarations := ← IO.mkRef {} }

def Session.merge (session : Session) (declarations : NameMap Declaration) : IO Unit := do
  session.declarations.modify fun current => Std.TreeMap.union current declarations

def Session.missing (session : Session) (names : Array Name) : IO (Array Name) := do
  let cached ← session.declarations.get
  return names.filter fun name => !cached.contains name

private def describe (declarations : NameMap Declaration) (name : Name) : IO Declaration := do
  let some declaration := declarations.find? name |
    throw <| IO.userError s!"declaration '{name}' was not prepared"
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
    (query.upstream.find? (·.name == name) <|>
      query.downstream.find? (·.name == name)).map (·.moduleName)

def Index.queryNamesAt (index : Index) (target : Name)
    (limits : Limits := {}) : QueryNames :=
  {
    target
    upstream := index.upstream target limits.upstream
    downstream := index.downstream target limits.downstream
  }

def Session.describeNames (session : Session) (items : Array Name) :
    IO (Array Declaration) := do
  let declarations ← session.declarations.get
  items.mapM (describe declarations)

def Session.describeQuery (session : Session) (names : QueryNames) :
    IO QueryResult := do
  let declarations ← session.declarations.get
  return {
    target := ← describe declarations names.target
    upstream := ← names.upstream.mapM (describe declarations)
    downstream := ← names.downstream.mapM (describe declarations)
  }

end LeanReach
