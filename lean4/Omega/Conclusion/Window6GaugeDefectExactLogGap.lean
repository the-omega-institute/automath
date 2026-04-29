import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

/-- Paper-facing wrapper for the exact window-6 gauge volume and log-gap coefficients.
    thm:conclusion-window6-gauge-defect-exact-log-gap -/
theorem paper_conclusion_window6_gauge_defect_exact_log_gap :
    Nat.factorial 2 ^ 8 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9 =
      2 ^ 39 * 3 ^ 13 ∧
    (8 * 1 + 4 * (-1 : Int) + 9 * 5 = 49 ∧
      4 * 2 + 9 * (-1 : Int) = -1) := by
  refine ⟨?_, paper_window6_gauge_defect_coefficient_extraction⟩
  calc
    Nat.factorial 2 ^ 8 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9 =
        2 ^ 8 * 6 ^ 4 * 24 ^ 9 := window6_gauge_group_factorial_factors
    _ = 2 ^ 39 * 3 ^ 13 := window6_gauge_group_order

end Omega.Conclusion
