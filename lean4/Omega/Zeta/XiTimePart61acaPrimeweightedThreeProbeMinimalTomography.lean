import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part61aca-primeweighted-three-probe-minimal-tomography`. -/
theorem paper_xi_time_part61aca_primeweighted_three_probe_minimal_tomography
    (M11 M12 M22 v1 v2 v3 : ℝ) (hv1 : v1 = M11) (hv2 : v2 = M22)
    (hv3 : v3 = M11 + 2 * M12 + M22) :
    M11 = v1 ∧ M22 = v2 ∧ M12 = (v3 - v1 - v2) / 2 := by
  subst v1
  subst v2
  subst v3
  constructor
  · rfl
  constructor
  · rfl
  · ring

end Omega.Zeta
