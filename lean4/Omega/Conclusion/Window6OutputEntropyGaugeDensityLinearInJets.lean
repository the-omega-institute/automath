import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Paper label:
`cor:conclusion-window6-output-entropy-gauge-density-linear-in-jets`. -/
theorem paper_conclusion_window6_output_entropy_gauge_density_linear_in_jets
    (L3 L7 kappa6 g6 D : ℝ)
    (hlog2 : Real.log 2 = ((2 : ℝ) * L3 + L7) / 5)
    (hlog3 : Real.log 3 = ((9 : ℝ) * L3 + (2 : ℝ) * L7) / 10)
    (hkappa : kappa6 = ((11 : ℝ) / 8) * Real.log 2 + ((3 : ℝ) / 16) * Real.log 3)
    (hg : g6 = ((39 : ℝ) / 64) * Real.log 2 + ((13 : ℝ) / 64) * Real.log 3)
    (hD : D = kappa6 - Real.log ((64 : ℝ) / 21)) :
    kappa6 = ((23 : ℝ) / 32) * L3 + ((5 : ℝ) / 16) * L7 ∧
      g6 = ((273 : ℝ) / 640) * L3 + ((13 : ℝ) / 80) * L7 ∧
      D = -Real.log ((64 : ℝ) / 21) + ((23 : ℝ) / 32) * L3 +
        ((5 : ℝ) / 16) * L7 := by
  have hkappa_linear :
      kappa6 = ((23 : ℝ) / 32) * L3 + ((5 : ℝ) / 16) * L7 := by
    rw [hkappa, hlog2, hlog3]
    ring
  have hg_linear :
      g6 = ((273 : ℝ) / 640) * L3 + ((13 : ℝ) / 80) * L7 := by
    rw [hg, hlog2, hlog3]
    ring
  refine ⟨hkappa_linear, hg_linear, ?_⟩
  rw [hD, hkappa_linear]
  ring

end

end Omega.Conclusion
