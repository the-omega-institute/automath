import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-short-long-sector-moments-closed`. -/
theorem paper_conclusion_window6_short_long_sector_moments_closed (s : ℝ) (hs : 0 ≤ s) :
    let short : List ℝ := [2, 4, 4, 4, 4, 4]
    let long : List ℝ := [2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4]
    (short.map (fun d => Real.rpow d s)).sum = Real.rpow 2 s + 5 * Real.rpow 4 s ∧
      (long.map (fun d => Real.rpow d s)).sum =
        4 * (Real.rpow 2 s + Real.rpow 3 s + Real.rpow 4 s) := by
  have _ := hs
  norm_num
  constructor <;> ring_nf

end Omega.Conclusion
