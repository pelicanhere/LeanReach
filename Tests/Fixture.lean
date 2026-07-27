import Lean

namespace LeanReachFixture

def double (n : Nat) : Nat := n + n

theorem double_eq_add (n : Nat) : double n = n + n := rfl

theorem double_zero : double 0 = 0 := rfl

theorem double_zero_again : double 0 = 0 := double_zero

structure Box where
  value : Nat

inductive Color where
  | red
  | blue

end LeanReachFixture
