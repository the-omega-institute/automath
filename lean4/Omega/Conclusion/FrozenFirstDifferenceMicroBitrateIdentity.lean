import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Conclusion.ConclusionFrozenFirstDifferenceRecoversMaxfiberExponent
import Omega.Conclusion.DeepfrozenMicroescortOracleThreshold

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-frozen-first-difference-micro-bitrate-identity`. -/
theorem paper_conclusion_frozen_first_difference_micro_bitrate_identity (a : ℤ)
    (alpha_star eta : ℝ) (B : ℕ → ℝ) (P : ℤ → ℝ) (heta : 0 < eta ∧ eta < 1)
    (hMicro :
      Tendsto (fun m : ℕ => B m / (m : ℝ)) atTop
        (nhds ((P a - P (a - 1)) / Real.log 2)))
    (hDiff : P a - P (a - 1) = alpha_star) :
    Tendsto (fun m : ℕ => B m / (m : ℝ)) atTop (nhds (alpha_star / Real.log 2)) := by
  have _hetaBounds : 0 < eta ∧ eta < 1 := heta
  simpa [hDiff] using hMicro

end Omega.Conclusion
