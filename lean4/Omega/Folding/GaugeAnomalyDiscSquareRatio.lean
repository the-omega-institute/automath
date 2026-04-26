import Mathlib.Tactic

namespace Omega.Folding

/-- The audited discriminant of the degree-10 branch polynomial `P10`. -/
def gaugeAnomalyDiscP10 : ℚ :=
  2 ^ 38 * 3 ^ 24 * 5 ^ 2 * 1931 * 9013 ^ 2 * 34319 ^ 3

/-- The audited discriminant of the degree-10 Tschirnhaus polynomial `Q10`. -/
def gaugeAnomalyDiscQ10 : ℚ :=
  2 ^ 42 * 3 ^ 16 * 5 ^ 8 * 1931 * 34319

/-- Paper label: `cor:fold-gauge-anomaly-disc-square-ratio`. -/
theorem paper_fold_gauge_anomaly_disc_square_ratio :
    gaugeAnomalyDiscP10 / gaugeAnomalyDiscQ10 = (((25054688907 : ℚ) / 500) ^ 2) := by
  norm_num [gaugeAnomalyDiscP10, gaugeAnomalyDiscQ10]

end Omega.Folding
