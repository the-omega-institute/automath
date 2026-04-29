import Mathlib.Tactic

namespace Omega.EA.StableAddCommutativeMonoid

/-- Transport of the additive commutative monoid laws from `Nat` along a bijective value map.
    thm:stable-add-commutative-monoid -/
theorem paper_stable_add_commutative_monoid {X : Type*} (op : X → X → X) (zero : X)
    (Val : X → Nat) (hbij : Function.Bijective Val) (hzero : Val zero = 0)
    (hop : ∀ x y, Val (op x y) = Val x + Val y) :
    (∀ x, op zero x = x ∧ op x zero = x) ∧
    (∀ x y, op x y = op y x) ∧
    (∀ x y z, op (op x y) z = op x (op y z)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · apply hbij.1
      simp [hop, hzero]
    · apply hbij.1
      simp [hop, hzero]
  · intro x y
    apply hbij.1
    simp [hop, Nat.add_comm]
  · intro x y z
    apply hbij.1
    simp [hop, Nat.add_assoc]

end Omega.EA.StableAddCommutativeMonoid
