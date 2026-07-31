import Lean.Data.Name

namespace LeanReach

open Lean

universe u

structure LocatedName where
  name : Name
  moduleName : Name
  deriving Inhabited

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
