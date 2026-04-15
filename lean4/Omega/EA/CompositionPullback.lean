import Omega.Folding.FiberArithmetic

namespace Omega.EA

open Omega X

/-- Composition pullback for addition: when a + b < F(m+2), stable addition
    on X m agrees with plain addition via ofNat.
    cor:composition-pullback -/
theorem compositionPullback_add (m a b : ℕ) (ha : a + b < Nat.fib (m + 2)) :
    X.stableAdd (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a + b) := by
  have hab : a < Nat.fib (m + 2) := Nat.lt_of_le_of_lt (Nat.le_add_right a b) ha
  have hb : b < Nat.fib (m + 2) := Nat.lt_of_le_of_lt (Nat.le_add_left b a) ha
  unfold stableAdd
  rw [stableValue_ofNat_lt a hab, stableValue_ofNat_lt b hb, Nat.mod_eq_of_lt ha]

/-- Composition pullback for multiplication: when a * b < F(m+2), stable multiplication
    on X m agrees with plain multiplication via ofNat.
    cor:composition-pullback -/
theorem compositionPullback_mul (m a b : ℕ) (hab : a * b < Nat.fib (m + 2)) :
    X.stableMul (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a * b) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [Nat.zero_mul] at hab ⊢
    unfold stableMul
    rw [stableValue_ofNat_lt 0 (fib_succ_pos (m + 1)), Nat.zero_mul, Nat.zero_mod]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp only [Nat.mul_zero] at hab ⊢
    unfold stableMul
    rw [stableValue_ofNat_lt 0 (fib_succ_pos (m + 1)), Nat.mul_zero, Nat.zero_mod]
  have ha' : a < Nat.fib (m + 2) := lt_of_le_of_lt (Nat.le_mul_of_pos_right a hb) hab
  have hb' : b < Nat.fib (m + 2) := lt_of_le_of_lt (Nat.le_mul_of_pos_left b ha) hab
  unfold stableMul
  rw [stableValue_ofNat_lt a ha', stableValue_ofNat_lt b hb', Nat.mod_eq_of_lt hab]

/-- Paper package: cor:composition-pullback -/
theorem paper_composition_pullback (m : ℕ) :
    (∀ a b : ℕ, a + b < Nat.fib (m + 2) →
      X.stableAdd (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a + b)) ∧
    (∀ a b : ℕ, a * b < Nat.fib (m + 2) →
      X.stableMul (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a * b)) := by
  exact ⟨compositionPullback_add m, compositionPullback_mul m⟩

/-- Paper package: cor:composition-pullback -/
theorem paper_composition_pullback_package (m : ℕ) :
    (∀ a b : ℕ, a + b < Nat.fib (m + 2) →
      X.stableAdd (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a + b)) ∧
    (∀ a b : ℕ, a * b < Nat.fib (m + 2) →
      X.stableMul (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a * b)) :=
  paper_composition_pullback m

end Omega.EA
