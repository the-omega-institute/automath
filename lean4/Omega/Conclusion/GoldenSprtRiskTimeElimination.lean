import Mathlib.Analysis.SpecialFunctions.Log.Base
import Omega.Conclusion.GoldenSprtDeltaClosure

namespace Omega.Conclusion

/-- Eliminating the SPRT threshold parameter `T` rewrites the expected time entirely in terms of
the golden `φ`-error curve and the base-`φ` log-likelihood ratio.
    thm:conclusion-golden-sprt-risk-time-elimination -/
theorem paper_conclusion_golden_sprt_risk_time_elimination (T : ℝ) :
    goldenSprtTimePhi T =
      Real.goldenRatio ^ (3 : ℝ) * (1 - 2 * goldenSprtErrorPhi T) *
        Real.logb Real.goldenRatio ((1 - goldenSprtErrorPhi T) / goldenSprtErrorPhi T) := by
  have hφ_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hφ_ne_one : Real.goldenRatio ≠ 1 := ne_of_gt Real.one_lt_goldenRatio
  have hsum_ne : 1 + Real.goldenRatio ^ T ≠ 0 := by positivity
  have hratio : (1 - goldenSprtErrorPhi T) / goldenSprtErrorPhi T = Real.goldenRatio ^ T := by
    unfold goldenSprtErrorPhi
    field_simp [hsum_ne]
    ring
  have hcontrast :
      1 - 2 * goldenSprtErrorPhi T =
        (Real.goldenRatio ^ T - 1) / (Real.goldenRatio ^ T + 1) := by
    unfold goldenSprtErrorPhi
    field_simp [hsum_ne]
    ring
  have hlogb : Real.logb Real.goldenRatio (Real.goldenRatio ^ T) = T := by
    simpa using Real.logb_rpow (b := Real.goldenRatio) (x := T) hφ_pos hφ_ne_one
  rw [goldenSprtTimePhi, hcontrast, hratio, hlogb]
  ring

end Omega.Conclusion
