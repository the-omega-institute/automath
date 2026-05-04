import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-bivariate-fisher-sharp`. -/
theorem paper_conclusion_poisson_bivariate_fisher_sharp (A B : ℝ) :
    4 * (A ^ 2 / 8 + B ^ 2 / 2) = A ^ 2 / 2 + 2 * B ^ 2 := by
  ring

end Omega.Conclusion
