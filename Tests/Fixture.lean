import Lean

namespace LeanReachFixture

def double (n : Nat) : Nat := n + n

theorem double_eq_add (n : Nat) : double n = n + n := rfl

theorem double_zero : double 0 = 0 := rfl

end LeanReachFixture
