import Lean

namespace LeanReachFixture

def double (n : Nat) : Nat := n + n

theorem double_eq_add (n : Nat) : double n = n + n := rfl

theorem double_zero : double 0 = 0 := rfl

theorem double_zero_again : double 0 = 0 := double_zero

private theorem hidden_double_zero : double 0 = 0 := double_zero

theorem double_zero_via_private : double 0 = 0 := hidden_double_zero

private def hiddenDouble (n : Nat) : Nat := n + n

def doubleViaPrivate (n : Nat) : Nat := hiddenDouble n

namespace Topic

theorem nearby : double 0 = 0 := double_zero

end Topic

namespace Generic

theorem helper : double 0 = 0 := double_zero

end Generic

namespace Topic

theorem ranked : double 0 = 0 ∧ double 0 = 0 := ⟨nearby, Generic.helper⟩

end Topic

structure Box where
  value : Nat

inductive Color where
  | red
  | blue

namespace Topic

theorem duplicateLeaf : double 0 = 0 := double_zero

end Topic

namespace Generic

theorem duplicateLeaf : double 0 = 0 := double_zero

end Generic

end LeanReachFixture
