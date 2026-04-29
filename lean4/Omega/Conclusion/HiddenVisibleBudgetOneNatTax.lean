import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hidden-visible-budget-one-nat-tax`. -/
theorem paper_conclusion_hidden_visible_budget_one_nat_tax
    (m : ℕ) (g κ h_hid h_vis err : ℝ)
    (hκ : (Real.log 2) * h_hid = κ)
    (hg : g = κ - 1 + err)
    (hvis : h_vis = (m : ℝ) - h_hid) :
    g = (Real.log 2) * h_hid - 1 + err ∧
      g = (m : ℝ) * Real.log 2 - (Real.log 2) * h_vis - 1 + err := by
  constructor
  · rw [hg, ← hκ]
  · calc
      g = (Real.log 2) * h_hid - 1 + err := by
        rw [hg, ← hκ]
      _ = (m : ℝ) * Real.log 2 - (Real.log 2) * h_vis - 1 + err := by
        rw [hvis]
        ring

end Omega.Conclusion
