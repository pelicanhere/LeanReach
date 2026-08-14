import Lean.Data.Name
import Lean.Data.NameMap

namespace LeanReach

open Lean

universe u v

inductive EdgeKind where
  | typeDependency
  | bodyDependency
  deriving Inhabited, BEq, Repr

structure Dependencies (α : Type u) where
  typeDeps : Array α := #[]
  bodyDeps : Array α := #[]
  deriving Inhabited, BEq

def Dependencies.all {α : Type u} (dependencies : Dependencies α) : Array α :=
  dependencies.typeDeps ++ dependencies.bodyDeps

def Dependencies.size {α : Type u} (dependencies : Dependencies α) : Nat :=
  dependencies.typeDeps.size + dependencies.bodyDeps.size

def Dependencies.map {α : Type u} {β : Type v} (f : α → β)
    (dependencies : Dependencies α) : Dependencies β := {
  typeDeps := dependencies.typeDeps.map f
  bodyDeps := dependencies.bodyDeps.map f
}

structure LocatedName where
  name : Name
  moduleName : Name
  deriving Inhabited

def LocatedName.sortByName (items : Array LocatedName) : Array LocatedName :=
  items.qsort fun left right => Name.lt left.name right.name

def groupNamesByModule (moduleOf? : Name → Option Name)
    (names : Array Name) : NameMap (Array Name) :=
  names.foldl (init := {}) fun groups name =>
    match moduleOf? name with
    | none => groups
    | some moduleName => groups.alter moduleName fun names =>
      some ((names.getD #[]).push name)

structure Neighborhood (α : Type u) where
  target : α
  upstream : Array α
  downstream : Array α
  deriving Inhabited, BEq

def Neighborhood.all {α : Type u} (items : Neighborhood α) : Array α :=
  (Array.mkEmpty (items.upstream.size + items.downstream.size + 1))
    |>.push items.target
    |>.append items.upstream
    |>.append items.downstream

structure Limits where
  upstream : Nat := 10
  downstream : Nat := 10
  search : Nat := 10

def Limits.uniform (limit : Nat) : Limits :=
  { upstream := limit, downstream := limit, search := limit }

end LeanReach
