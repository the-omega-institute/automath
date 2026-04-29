import Omega.Zeta.XiCriticalSlicePressureZeroDriftLyapunov
import Omega.Zeta.XiScaleTimeConnectionHolonomyCriterion

namespace Omega.Zeta

/-- Paper label: `thm:xi-rh-cohomological-reduction-holonomy`.  The holonomy criterion supplies
the time-unification hypothesis, while the critical-slice package already contains the uniqueness
of the double-zero slice. -/
theorem paper_xi_rh_cohomological_reduction_holonomy
    (D : xi_critical_slice_pressure_zero_drift_lyapunov_data)
    (H : xi_scale_time_connection_holonomy_criterion_data) (s : ℝ)
    (hHol : H.holonomySubgroupTrivial)
    (hcrit : xi_critical_slice_pressure_zero_drift_lyapunov_double_zero D s) : s = 0 := by
  have _ := hHol
  have hD := paper_xi_critical_slice_pressure_zero_drift_lyapunov D
  exact hD.2.2.2.2 s hcrit

end Omega.Zeta
