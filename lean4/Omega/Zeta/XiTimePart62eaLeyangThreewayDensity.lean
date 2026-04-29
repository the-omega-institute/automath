import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62ea-A-leyang-threeway-density`. -/
theorem paper_xi_time_part62ea_a_leyang_threeway_density :
    ((28319 : ℚ) / 44800) * ((1 : ℚ) / 6) = (28319 : ℚ) / 268800 ∧
      ((28319 : ℚ) / 44800) * ((1 : ℚ) / 2) = (28319 : ℚ) / 89600 ∧
        ((28319 : ℚ) / 44800) * ((1 : ℚ) / 3) = (28319 : ℚ) / 134400 := by
  norm_num

end Omega.Zeta
