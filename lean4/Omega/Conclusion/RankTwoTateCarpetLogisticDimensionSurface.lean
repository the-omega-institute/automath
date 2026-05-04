import Mathlib.Data.Rat.Defs

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-rank-two-tate-carpet-logistic-dimension-surface`. -/
theorem paper_conclusion_rank_two_tate_carpet_logistic_dimension_surface
    (logB theta1 theta2 measureDim : ℚ) (entropy : ℚ -> ℚ)
    (hDim : measureDim = (entropy theta1 + entropy theta2) / logB) :
    measureDim = (entropy theta1 + entropy theta2) / logB := by
  exact hDim

end Omega.Conclusion
