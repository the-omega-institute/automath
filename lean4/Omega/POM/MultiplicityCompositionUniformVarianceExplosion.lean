import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-multiplicity-composition-uniform-variance-explosion`. -/
theorem paper_pom_multiplicity_composition_uniform_variance_explosion (L : ℕ)
    (Z1 Z2 C mean second variance : ℝ) (hZ1 : Z1 ≠ 0)
    (hpow : (2 : ℝ) ^ (L - 1) ≠ 0) (hmean : mean = Z1 / (2 : ℝ) ^ (L - 1))
    (hsecond : second = Z2 / (2 : ℝ) ^ (L - 1))
    (hvariance : variance = second - mean ^ 2) (hC : C = Z2 / Z1 ^ 2) :
    mean = Z1 / (2 : ℝ) ^ (L - 1) ∧ second = Z2 / (2 : ℝ) ^ (L - 1) ∧
      variance / mean ^ 2 = (2 : ℝ) ^ (L - 1) * Z2 / Z1 ^ 2 - 1 := by
  have _hC : C = Z2 / Z1 ^ 2 := hC
  have hmean_ne : mean ≠ 0 := by
    rw [hmean]
    exact div_ne_zero hZ1 hpow
  refine ⟨hmean, hsecond, ?_⟩
  rw [hvariance, hmean, hsecond]
  field_simp [hZ1, hpow]

end Omega.POM
