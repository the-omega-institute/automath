import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-window6-b3c3-weyl-average-measure-second-moment`. -/
theorem paper_xi_window6_b3c3_weyl_average_measure_second_moment (mB mC a b : ℚ)
    (hB : mB = a * 1 + (1 - a) * 2) (hC : mC = b * 2 + (1 - b) * 4) :
    a = 2 - mB ∧ 1 - a = mB - 1 ∧ b = (4 - mC) / 2 ∧ 1 - b = (mC - 2) / 2 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end Omega.Zeta
