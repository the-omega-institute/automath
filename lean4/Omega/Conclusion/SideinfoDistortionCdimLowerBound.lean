import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-sideinfo-distortion-cdim-lower-bound`. -/
theorem paper_conclusion_sideinfo_distortion_cdim_lower_bound
    (L cdim logQ rate logX : ℝ) (hLower : rate - logX ≤ L)
    (hBudget : L ≤ cdim * logQ) (hlogQ : 0 < logQ) :
    (rate - logX) / logQ ≤ cdim := by
  rw [div_le_iff₀ hlogQ]
  linarith

end Omega.Conclusion
