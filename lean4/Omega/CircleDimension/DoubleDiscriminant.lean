import Mathlib.Tactic

/-!
# Double discriminant two-parameter family seed values

Power and factorial identities for the double discriminant synchronization family.
-/

namespace Omega.CircleDimension

/-- Double discriminant two-parameter seeds.
    prop:cdim-double-discriminant-two-parameter-family -/
theorem paper_cdim_double_discriminant_two_parameter_seeds :
    (2 = 2) ∧
    (256 = 4 ^ 4 ∧ 4 * 4 * 4 * 4 = 256) ∧
    (2 - 1 = 1) ∧
    (4 * 3 * 2 * 1 = 24) ∧
    (3 - 1 = 2) := by
  omega

/-- Package wrapper for the double discriminant two-parameter seeds.
    prop:cdim-double-discriminant-two-parameter-family -/
theorem paper_cdim_double_discriminant_two_parameter_package :
    (2 = 2) ∧
    (256 = 4 ^ 4 ∧ 4 * 4 * 4 * 4 = 256) ∧
    (2 - 1 = 1) ∧
    (4 * 3 * 2 * 1 = 24) ∧
    (3 - 1 = 2) :=
  paper_cdim_double_discriminant_two_parameter_seeds

/-- Paper-facing parity and integrality constraint for the two sign branches of the
double-discriminant two-parameter family.
    prop:cdim-double-discriminant-two-parameter-family -/
theorem paper_cdim_double_discriminant_two_parameter_family (a b : ℤ) (ha : Even a)
    (hb : Odd b) :
    (∀ x : ℤ, 4 ∣ ((2 * x ^ 2 + a * x + b) ^ 2 - (4 * x ^ 3 - 4 * x + 1))) ∧
      (∀ x : ℤ, 4 ∣ ((-2 * x ^ 2 + a * x + b) ^ 2 - (4 * x ^ 3 - 4 * x + 1))) := by
  rcases ha with ⟨c, rfl⟩
  rcases hb with ⟨d, rfl⟩
  constructor
  · intro x
    refine ⟨(x ^ 2 + c * x + d) ^ 2 + (x ^ 2 + c * x + d) - x ^ 3 + x, ?_⟩
    ring
  · intro x
    refine ⟨(-x ^ 2 + c * x + d) ^ 2 + (-x ^ 2 + c * x + d) - x ^ 3 + x, ?_⟩
    ring

end Omega.CircleDimension
