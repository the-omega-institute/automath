import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-volume-entropy-state-equation`. -/
theorem paper_xi_time_volume_entropy_state_equation (p h_vol : ℝ) (h : p = h_vol - 1) :
    h_vol = p + 1 := by
  linarith

end Omega.Zeta
