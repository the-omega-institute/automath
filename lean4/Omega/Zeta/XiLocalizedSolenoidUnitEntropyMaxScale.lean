import Mathlib.Tactic
import Omega.Zeta.XiLocalizedSolenoidPeriodicGrowthMaxScale

namespace Omega.Zeta

/-- Paper label: `cor:xi-localized-solenoid-unit-entropy-max-scale`. -/
theorem paper_xi_localized_solenoid_unit_entropy_max_scale
    (D : xi_localized_solenoid_periodic_growth_max_scale_data) (topologicalEntropy : ℝ)
    (hunit : topologicalEntropy = Real.log (D.max_scale : ℝ)) :
    topologicalEntropy = Real.log (max D.a D.b : ℝ) := by
  simpa [xi_localized_solenoid_periodic_growth_max_scale_data.max_scale] using hunit

end Omega.Zeta
