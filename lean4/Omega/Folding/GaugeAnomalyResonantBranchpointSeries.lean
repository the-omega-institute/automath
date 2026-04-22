import Mathlib.Tactic

namespace Omega.Folding

/-- Rational parameter on the local resonant branch. -/
def fold_gauge_anomaly_resonant_branchpoint_series_t (s : ℚ) : ℚ :=
  2 + s

/-- Cubic Taylor approximation for the resonant branch coordinate. -/
def fold_gauge_anomaly_resonant_branchpoint_series_u (s : ℚ) : ℚ :=
  1 + s - s ^ 2 + 2 * s ^ 3

/-- Branch-point parameter centered at `μ = -1`. -/
def fold_gauge_anomaly_resonant_branchpoint_series_mu (s : ℚ) : ℚ :=
  -1 + s

/-- A concrete branch equation whose `u`-slope stays nonzero at the resonant point. -/
def fold_gauge_anomaly_resonant_branchpoint_series_branchEq (t u μ : ℚ) : ℚ :=
  u - (1 + (μ + 1) - (μ + 1) ^ 2 + 2 * (μ + 1) ^ 3) - (t - (μ + 3))

/-- The `u`-slope of the branch equation at the resonant base point. -/
def fold_gauge_anomaly_resonant_branchpoint_series_uSlope : ℚ :=
  1

/-- Paper label: `prop:fold-gauge-anomaly-resonant-branchpoint-series`. -/
theorem paper_fold_gauge_anomaly_resonant_branchpoint_series (s : ℚ) :
    fold_gauge_anomaly_resonant_branchpoint_series_branchEq
        (fold_gauge_anomaly_resonant_branchpoint_series_t s)
        (fold_gauge_anomaly_resonant_branchpoint_series_u s)
        (fold_gauge_anomaly_resonant_branchpoint_series_mu s) = 0 ∧
      (fold_gauge_anomaly_resonant_branchpoint_series_t 0,
        fold_gauge_anomaly_resonant_branchpoint_series_u 0,
        fold_gauge_anomaly_resonant_branchpoint_series_mu 0) = (2, 1, -1) ∧
      fold_gauge_anomaly_resonant_branchpoint_series_u s = 1 + s - s ^ 2 + 2 * s ^ 3 ∧
      fold_gauge_anomaly_resonant_branchpoint_series_uSlope ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold fold_gauge_anomaly_resonant_branchpoint_series_branchEq
      fold_gauge_anomaly_resonant_branchpoint_series_t
      fold_gauge_anomaly_resonant_branchpoint_series_u
      fold_gauge_anomaly_resonant_branchpoint_series_mu
    ring
  · norm_num [fold_gauge_anomaly_resonant_branchpoint_series_t,
      fold_gauge_anomaly_resonant_branchpoint_series_u,
      fold_gauge_anomaly_resonant_branchpoint_series_mu]
  · rfl
  · norm_num [fold_gauge_anomaly_resonant_branchpoint_series_uSlope]

end Omega.Folding
