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
  #[items.target] ++ items.upstream ++ items.downstream

end LeanReach
