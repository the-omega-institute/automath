import Mathlib
import Omega.POM.ParryTwoPointAlternating

namespace Omega.POM

noncomputable section

/-- The subleading spectral radius for the golden-mean Parry chain. -/
def pomTimeCorrGapRate : Real :=
  1 / (Real.goldenRatio ^ 2)

/-- The covariance prefactor coming from the stationary masses `π₀ π₁`. -/
def pomTimeCorrGapPrefactor : Real :=
  Real.goldenRatio ^ 2 / (Real.goldenRatio ^ 2 + 1) ^ 2

/-- Paper label: `prop:pom-time-corr-gap`.
For the explicit golden-mean Parry chain, the time-correlation envelope is exactly the product of
the prefactor `π₀ π₁` and the `k`-th power of the subleading spectral radius. -/
theorem paper_pom_time_corr_gap (k : ℕ) :
    |parryCovariance k| = pomTimeCorrGapPrefactor * pomTimeCorrGapRate ^ k := by
  have hphi_sq_pos : 0 < Real.goldenRatio ^ 2 + 1 := by positivity
  have hrate_nonneg : 0 ≤ 1 / (Real.goldenRatio ^ 2) := by positivity
  unfold parryCovariance pomTimeCorrGapPrefactor pomTimeCorrGapRate
  rw [abs_mul, abs_mul, abs_pow]
  rw [abs_of_nonneg]
  rw [abs_of_nonneg]
  rw [abs_neg, abs_of_nonneg hrate_nonneg]
  · field_simp [hphi_sq_pos.ne']
  · positivity
  · positivity

end

end Omega.POM
