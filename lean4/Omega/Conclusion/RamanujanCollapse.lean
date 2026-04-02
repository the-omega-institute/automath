import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Conclusion

/-- Ramanujan half-dimension collapse: log(2/√φ)/log(φ) = log(2)/log(φ) - 1/2.
    cor:discussion-ramanujan-half-dimension-collapse -/
theorem ramanujan_half_dimension_collapse :
    Real.log (2 / Real.sqrt Real.goldenRatio) / Real.log Real.goldenRatio
    = Real.log 2 / Real.log Real.goldenRatio - 1 / 2 := by
  have hφ_pos := Real.goldenRatio_pos
  have hsqrt_pos := Real.sqrt_pos_of_pos hφ_pos
  have hsqrt_ne : Real.sqrt Real.goldenRatio ≠ 0 := ne_of_gt hsqrt_pos
  have hlog_ne : Real.log Real.goldenRatio ≠ 0 := ne_of_gt (Real.log_pos Real.one_lt_goldenRatio)
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hsqrt_ne,
    Real.log_sqrt (le_of_lt hφ_pos)]
  field_simp

/-- Paper: cor:discussion-ramanujan-half-dimension-collapse -/
theorem paper_ramanujan_half_dimension_collapse :
    Real.log (2 / Real.sqrt Real.goldenRatio) / Real.log Real.goldenRatio
    = Real.log 2 / Real.log Real.goldenRatio - 1 / 2 :=
  ramanujan_half_dimension_collapse

end Omega.Conclusion
