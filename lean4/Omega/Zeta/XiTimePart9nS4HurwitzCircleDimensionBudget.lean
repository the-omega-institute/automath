import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9n-s4-hurwitz-circle-dimension-budget`. -/
theorem paper_xi_time_part9n_s4_hurwitz_circle_dimension_budget :
    (10 = 2 * 5) ∧ (8 = 2 * 4) ∧ (6 = 2 * 3) ∧ (18 = 2 * 9) ∧
      (26 = 2 * 13) ∧ (98 = 2 * 49) ∧ (10 + 2 * 8 + 3 * 6 + 3 * 18 = 98) := by
  norm_num

end Omega.Zeta
