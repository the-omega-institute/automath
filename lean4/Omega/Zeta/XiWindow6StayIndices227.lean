import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-window6-stay-indices-22-7`. -/
theorem paper_xi_window6_stay_indices_22_7 :
    ((1 : ℚ) / ((28 : ℚ) / 81) = 81 / 28) ∧
      ((1 : ℚ) / ((7 : ℚ) / 22) = 22 / 7) ∧
      ((1 : ℚ) / ((2 : ℚ) / 27) = 27 / 2) ∧
      ((1 : ℚ) / ((1 : ℚ) / 9) = 9) := by
  norm_num

end Omega.Zeta
