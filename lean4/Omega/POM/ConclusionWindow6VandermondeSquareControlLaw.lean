import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:conclusion-window6-vandermonde-square-control-law`. -/
theorem paper_conclusion_window6_vandermonde_square_control_law :
    (((2 - 3) * (2 - 4) * (3 - 4) : ℤ) = -2) ∧
      ((((2 - 3) * (2 - 4) * (3 - 4) : ℤ) ^ 2) = 4) := by
  norm_num

end Omega.POM
