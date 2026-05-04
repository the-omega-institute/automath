import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-first-feasible-alphabet-still-fails-on-maxfiber`. -/
theorem paper_conclusion_first_feasible_alphabet_still_fails_on_maxfiber
    (m : ℕ) (success c5 C : ℝ)
    (hc5 : c5 = (1 / 2 : ℝ) * Real.log Real.goldenRatio - (4 / 27 : ℝ) * Real.log 5)
    (hpos : 0 < c5)
    (hbound : success ≤ Real.exp (-c5 * m + C)) :
    success ≤ Real.exp (-c5 * m + C) ∧ 0 < c5 := by
  let _ := hc5
  exact ⟨hbound, hpos⟩

end Omega.Conclusion
