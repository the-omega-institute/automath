import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyPressureCumulants5

namespace Omega.Folding

/-- The third gauge-anomaly cumulant is the explicit negative rational constant recorded in the
order-five pressure-cumulant package.
    cor:fold-gauge-anomaly-cumulant3 -/
theorem paper_fold_gauge_anomaly_cumulant3 (h : GaugeAnomalyPressureCumulantsFiveData) :
    h.kappa 3 = (-1174 / 2187 : ℚ) ∧ h.kappa 3 < 0 := by
  refine ⟨h.kappa_three, ?_⟩
  rw [h.kappa_three]
  norm_num

end Omega.Folding
