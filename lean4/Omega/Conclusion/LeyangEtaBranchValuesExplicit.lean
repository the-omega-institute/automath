import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-eta-branch-values-explicit`. -/
theorem paper_conclusion_leyang_eta_branch_values_explicit (η : ℝ) :
    2304 * η ^ 4 - 8896 * η ^ 3 + 13157 * η ^ 2 - 8896 * η + 2304 =
      2304 *
        ((η ^ 2 - (((139 : ℝ) / 72 + 7 * Real.sqrt 7 / 144) * η) + 1) *
          (η ^ 2 - (((139 : ℝ) / 72 - 7 * Real.sqrt 7 / 144) * η) + 1)) := by
  have hsqrt : (Real.sqrt 7) ^ 2 = (7 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hsqrt]
  ring_nf

end Omega.Conclusion
