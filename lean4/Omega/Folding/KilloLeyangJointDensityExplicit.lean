import Mathlib.Tactic

namespace Omega.Folding

/-- Paper label: `cor:killo-leyang-joint-density-explicit`. -/
theorem paper_killo_leyang_joint_density_explicit :
    ((28319 : ℚ) / 44800) * (1 / 6 : ℚ) = 28319 / 268800 ∧
      ((28319 : ℚ) / 44800) * (2 / 3 : ℚ) = 28319 / 67200 := by
  constructor <;> norm_num

end Omega.Folding
