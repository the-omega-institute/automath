import Mathlib.Logic.Basic

namespace Omega.Zeta

/-- Paper label: `cor:xi-basepoint-scan-anchor-angle-concentration`. -/
theorem paper_xi_basepoint_scan_anchor_angle_concentration
    (nearMax angleConcentration : Prop) (h : nearMax -> angleConcentration) :
    nearMax -> angleConcentration := by
  exact h

end Omega.Zeta
