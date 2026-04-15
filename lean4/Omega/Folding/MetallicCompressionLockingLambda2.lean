import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Folding

/-- The metallic Perron root from the continuous parameter `A`. -/
noncomputable def metallicPerronRoot (A : ℝ) : ℝ :=
  (A + Real.sqrt (A ^ 2 + 4)) / 2

/-- The compression slope written in terms of the metallic Perron root. -/
noncomputable def metallicCompressionSlope (A : ℝ) : ℝ :=
  Real.log ((A + 1) / metallicPerronRoot A)

/-- Paper-facing locking corollary: at the extremal parameter `A = 3/2`, the metallic Perron
root is exactly `2`, and the compression slope becomes the closed form `log (5/4)`.
    cor:metallic-compression-locking-lambda2 -/
theorem paper_metallic_compression_locking_lambda2 :
    metallicPerronRoot (3 / 2 : ℝ) = 2 ∧
      metallicCompressionSlope (3 / 2 : ℝ) = Real.log (5 / 4) := by
  have hsqrt : Real.sqrt (((3 / 2 : ℝ) ^ 2 + 4)) = 5 / 2 := by
    rw [show ((3 / 2 : ℝ) ^ 2 + 4) = (5 / 2) ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs]
    norm_num
  have hroot : metallicPerronRoot (3 / 2 : ℝ) = 2 := by
    rw [metallicPerronRoot, hsqrt]
    norm_num
  refine ⟨hroot, ?_⟩
  rw [metallicCompressionSlope, hroot]
  congr 1
  norm_num

end Omega.Folding
