import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-cauchy-universal-quartic-information-metric`.
The three sharp quartic coefficients are packaged by the same quadratic form. -/
theorem paper_conclusion_poisson_cauchy_universal_quartic_information_metric {A B KL fdiv Fisher fpp : ℝ}
    (hKL : KL = A ^ 2 / 8 + B ^ 2 / 2)
    (hFDiv : fdiv = fpp * (A ^ 2 / 8 + B ^ 2 / 2))
    (hFisher : Fisher = 4 * (A ^ 2 / 8 + B ^ 2 / 2)) :
    KL = A ^ 2 / 8 + B ^ 2 / 2 ∧ fdiv = fpp * (A ^ 2 / 8 + B ^ 2 / 2) ∧
      Fisher = 4 * (A ^ 2 / 8 + B ^ 2 / 2) := by
  exact ⟨hKL, hFDiv, hFisher⟩

end Omega.Conclusion
