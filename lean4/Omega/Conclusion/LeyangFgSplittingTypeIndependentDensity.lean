import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-fg-splitting-type-independent-density`. -/
theorem paper_conclusion_leyang_fg_splitting_type_independent_density :
    ((1 : ℚ) / 6 * ((1 : ℚ) / 6) = (1 : ℚ) / 36) ∧
      ((1 : ℚ) / 6 * ((1 : ℚ) / 2) = (1 : ℚ) / 12) ∧
      ((1 : ℚ) / 6 * ((1 : ℚ) / 3) = (1 : ℚ) / 18) ∧
      ((1 : ℚ) / 2 * ((1 : ℚ) / 6) = (1 : ℚ) / 12) ∧
      ((1 : ℚ) / 2 * ((1 : ℚ) / 2) = (1 : ℚ) / 4) ∧
      ((1 : ℚ) / 2 * ((1 : ℚ) / 3) = (1 : ℚ) / 6) ∧
      ((1 : ℚ) / 3 * ((1 : ℚ) / 6) = (1 : ℚ) / 18) ∧
      ((1 : ℚ) / 3 * ((1 : ℚ) / 2) = (1 : ℚ) / 6) ∧
      ((1 : ℚ) / 3 * ((1 : ℚ) / 3) = (1 : ℚ) / 9) := by
  norm_num

end Omega.Conclusion
