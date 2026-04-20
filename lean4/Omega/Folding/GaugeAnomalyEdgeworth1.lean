import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyCumulant3
import Omega.Folding.GaugeAnomalyVarianceFiniteWindowClosed

namespace Omega.Folding

/-- The standardized third cumulant of the gauge-anomaly pressure branch is the explicit rational
constant obtained by dividing the third cumulant by the square root of the variance cube.
    cor:fold-gauge-anomaly-edgeworth1 -/
theorem paper_fold_gauge_anomaly_edgeworth1 (h : Omega.Folding.GaugeAnomalyPressureCumulantsFiveData) :
    ((h.kappa 3 : ℝ) / Real.sqrt ((h.kappa 2 : ℝ) ^ 3)) =
      (((-1174 / 2187 : ℚ) : ℝ) / Real.sqrt ((((118 / 243 : ℚ) : ℝ) ^ 3))) := by
  rw [h.kappa_three, h.kappa_two]

end Omega.Folding
