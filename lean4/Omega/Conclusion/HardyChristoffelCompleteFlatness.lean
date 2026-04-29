import Mathlib.Tactic

namespace Omega.Conclusion

set_option linter.unusedVariables false in
/-- Paper label: `thm:conclusion-hardy-christoffel-complete-flatness`. -/
theorem paper_conclusion_hardy_christoffel_complete_flatness
    (N : ℕ) (hN : 1 ≤ N) (Kdiag minNorm : ℝ) (hKdiag : Kdiag = (N : ℝ))
    (hMin : minNorm = 1 / Kdiag) :
    minNorm = 1 / (N : ℝ) ∧ Kdiag = (N : ℝ) := by
  constructor
  · rw [hMin, hKdiag]
  · exact hKdiag

end Omega.Conclusion
