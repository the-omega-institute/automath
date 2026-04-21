import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40GroundEntropy

namespace Omega.SyncKernelWeighted

/-- The positive-entropy freezing endpoint is exactly the ground entropy `log c`, and the endpoint
rate rewrites as the golden-ratio normalization minus that entropy. -/
theorem paper_killo_real_input_40_positive_entropy_freezing (c : ℝ) (hc : 1 < c) :
    0 < Omega.SyncKernelWeighted.realInput40GroundEntropy c ∧
      Omega.SyncKernelWeighted.realInput40GroundEntropy c = Real.log c ∧
      Real.log (Real.goldenRatio ^ 2 / c) = Real.log (Real.goldenRatio ^ 2) -
        Omega.SyncKernelWeighted.realInput40GroundEntropy c := by
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  refine ⟨?_, rfl, ?_⟩
  · simpa [Omega.SyncKernelWeighted.realInput40GroundEntropy] using Real.log_pos hc
  · rw [Real.log_div (show Real.goldenRatio ^ 2 ≠ 0 by positivity) (show c ≠ 0 by linarith)]
    rfl

end Omega.SyncKernelWeighted
