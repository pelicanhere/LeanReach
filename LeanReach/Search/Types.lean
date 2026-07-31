import Lean.Data.Name
import Lean.Data.NameMap

namespace LeanReach

open Lean

universe u

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
