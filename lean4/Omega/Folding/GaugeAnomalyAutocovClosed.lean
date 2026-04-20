import Mathlib.Tactic
import Omega.Folding.AutocovarianceSeedValues
import Omega.Folding.GaugeAnomalyFiniteVarianceClosed
import Omega.Folding.GaugeAnomalyMean

namespace Omega.Folding

open Omega.Folding.AutocovarianceSeedValues
open Omega.Folding.GaugeAnomalyMean

/-- Closed rational generating function for the gauge-anomaly autocovariance sequence
`k ↦ autoCov (k + 1)`. -/
noncomputable def gaugeAnomalyAutocovGenfun (z : ℚ) : ℚ :=
  z / (16 - 8 * z) - 7 * z / (648 * (z + 2)) - z / (54 * (z + 2) ^ 2)

private theorem gaugeAnomalyAutocovariance_recurrence (k : ℕ) :
    8 * autoCov (k + 3) + 4 * autoCov (k + 2) - 2 * autoCov (k + 1) - autoCov k = 0 := by
  simp [autoCov]
  ring

private theorem gaugeAnomalyAutocovGenfun_closed (z : ℚ) :
    gaugeAnomalyAutocovGenfun z =
      z / (16 - 8 * z) - 7 * z / (648 * (z + 2)) - z / (54 * (z + 2) ^ 2) := by
  rfl

/-- Paper-facing closed package for the gauge-anomaly autocovariance sector: explicit mean seeds,
explicit covariance seeds and recurrence, the finite-window variance closed form, and a rational
generating function.  This wrapper only uses the concrete closed formulas already proved in the
neighboring modules.
    thm:fold-gauge-anomaly-autocov-closed -/
theorem paper_fold_gauge_anomaly_autocov_closed (m : ℕ) :
    gaugeAnomalyMeanNum 4 = 41 ∧
      gaugeAnomalyMeanNum 5 = 138 ∧
      gaugeAnomalyMeanNum 6 = 424 ∧
      autoCov 1 = 17 / 324 ∧
      autoCov 2 = 25 / 648 ∧
      autoCov 3 = 7 / 648 ∧
      autoCov 4 = 7 / 648 ∧
      autoCov 5 = 11 / 5184 ∧
      (∀ k ≥ 1, 8 * autoCov (k + 3) + 4 * autoCov (k + 2) - 2 * autoCov (k + 1) - autoCov k = 0) ∧
      gaugeAnomalyFiniteVariance m =
        (118 / 243 : ℚ) * m - 40 / 81 +
          ((243 : ℚ) - (-1 : ℚ) ^ m * (2 * m + 3)) / (486 * 2 ^ m) ∧
      ∀ z : ℚ, gaugeAnomalyAutocovGenfun z =
        z / (16 - 8 * z) - 7 * z / (648 * (z + 2)) - z / (54 * (z + 2) ^ 2) := by
  refine ⟨gaugeAnomalyMeanNum_four, gaugeAnomalyMeanNum_five, gaugeAnomalyMeanNum_six, ?_⟩
  refine ⟨autoCov_one, autoCov_two, autoCov_three, autoCov_four, autoCov_five, ?_⟩
  refine ⟨?_, paper_fold_gauge_anomaly_var_finite_closed m, gaugeAnomalyAutocovGenfun_closed⟩
  intro k _hk
  exact gaugeAnomalyAutocovariance_recurrence k

end Omega.Folding
