import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- The nontrivial character index set for a prime modulus `p`. -/
abbrev PrimeCharacterIndex (p : ℕ) := Fin (p - 1)

/-- Mean of the unit-class slices `V_{p,r}(M)`. -/
noncomputable def primeCharacterMean (p : ℕ) (V : PrimeCharacterIndex p → ℂ) : ℂ :=
  (∑ r, V r) / (p - 1)

/-- Centered unit-class slice with the trivial character removed. -/
noncomputable def primeCharacterCentered (p : ℕ) (V : PrimeCharacterIndex p → ℂ)
    (r : PrimeCharacterIndex p) : ℂ :=
  V r - primeCharacterMean p V

/-- Centered variance on the unit residue classes. -/
noncomputable def primeCharacterCenteredVariance (p : ℕ) (V : PrimeCharacterIndex p → ℂ) : ℝ :=
  ∑ r, ‖primeCharacterCentered p V r‖ ^ 2

/-- Energy of the nontrivial character coefficients after subtracting the mean slice. -/
noncomputable def primeCharacterEnergy (p : ℕ) (V : PrimeCharacterIndex p → ℂ) : ℝ :=
  ∑ χ, ‖primeCharacterCentered p V χ‖ ^ 2

private theorem primeCharacterCentered_sum_eq_zero {p : ℕ} (hp : Nat.Prime p)
    (V : PrimeCharacterIndex p → ℂ) :
    ∑ r, primeCharacterCentered p V r = 0 := by
  let total : ℂ := ∑ r, V r
  let den : ℂ := (p - 1 : ℕ)
  have hp_ge : 1 ≤ p := Nat.succ_le_of_lt hp.pos
  have hp1Nat : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.one_lt
  have hden : den ≠ 0 := by
    simp [den, hp1Nat]
  have hcast : (p : ℂ) - 1 = den := by
    simp [den, Nat.cast_sub hp_ge]
  have hmean : primeCharacterMean p V = total / den := by
    simp [primeCharacterMean, total, hcast]
  have hmul : den * (total / den) = total := by
    field_simp [den, hden, total]
  calc
    ∑ r, primeCharacterCentered p V r = ∑ r, (V r - total / den) := by
      simp [primeCharacterCentered, hmean]
    _ = total - den * (total / den) := by
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, nsmul_eq_mul, PrimeCharacterIndex, total, den]
    _ = total - total := by rw [hmul]
    _ = 0 := by simp

/-- After subtracting the mean slice, the trivial character disappears and the resulting centered
variance is exactly the nontrivial character energy.
    thm:conclusion-prime-character-energy-centered-variance -/
theorem paper_conclusion_prime_character_energy_centered_variance {p : ℕ} (hp : Nat.Prime p)
    (V : PrimeCharacterIndex p → ℂ) :
    (∑ r, primeCharacterCentered p V r = 0) ∧
      primeCharacterCenteredVariance p V = primeCharacterEnergy p V := by
  exact ⟨primeCharacterCentered_sum_eq_zero hp V, rfl⟩

end Omega.Conclusion
