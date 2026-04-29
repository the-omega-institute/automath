import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-s5-leyang-codimension-one-defect-line`. -/
theorem paper_conclusion_s5_leyang_codimension_one_defect_line
    (S T x y : ℝ) (hS : S = x + y) (hT : T = x + 2 * y) :
    y = T - S ∧ x = 2 * S - T := by
  constructor
  · nlinarith
  · nlinarith

end Omega.Conclusion
