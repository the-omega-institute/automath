import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-ground-entropy-half-topological-entropy`. -/
theorem paper_conclusion_realinput40_ground_entropy_half_topological_entropy
    (hground rho htop : ℝ) (hHalfPerron : hground = Real.log rho / 2)
    (hTop : htop = Real.log rho) :
    hground = Real.log rho / 2 ∧ hground = htop / 2 := by
  constructor
  · exact hHalfPerron
  · rw [hTop]
    exact hHalfPerron

end Omega.Conclusion
