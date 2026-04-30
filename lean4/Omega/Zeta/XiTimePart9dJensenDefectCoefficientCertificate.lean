import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9d-jensen-defect-coefficient-certificate`. -/
theorem paper_xi_time_part9d_jensen_defect_coefficient_certificate (D C r S : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) (hbridge : D ≤ C)
    (hC : C = (1 / 2) * ((1 + r) / (1 - r)) ^ 2 * S) :
    D ≤ (1 / 2) * ((1 + r) / (1 - r)) ^ 2 * S := by
  have _ : 0 < r := hr0
  have _ : r < 1 := hr1
  rw [← hC]
  exact hbridge

end Omega.Zeta
