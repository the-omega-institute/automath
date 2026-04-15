import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# One-sided monotonicity seed for metallic compression

This file records the paper-facing seed/package wrapper for
`prop:metallic-compression-extremum`.
-/

namespace Omega.Folding.MetallicCompressionExtremum

/-- Paper seed for the large-`A` side of the metallic-compression extremum:
    once `A > 3 / 2`, the metallic eigenvalue term lies strictly below `A + 1`.
    prop:metallic-compression-extremum -/
theorem paper_metallic_compression_extremum_seeds {A : ℝ} (hA : 3 / 2 < A) :
    (A + Real.sqrt (A^2 + 4)) / 2 < A + 1 := by
  have hA_pos : 0 < A := by nlinarith
  have hA2_nonneg : 0 ≤ A + 2 := by linarith
  have hsq : A ^ 2 + 4 < (A + 2) ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (A ^ 2 + 4) < A + 2 := by
    have h' : Real.sqrt (A ^ 2 + 4) < Real.sqrt ((A + 2) ^ 2) := by
      exact Real.sqrt_lt_sqrt (by nlinarith [sq_nonneg A]) hsq
    simpa [Real.sqrt_sq hA2_nonneg] using h'
  nlinarith

/-- Packaged form of the metallic-compression extremum seed.
    prop:metallic-compression-extremum -/
theorem paper_metallic_compression_extremum_package {A : ℝ} (hA : 3 / 2 < A) :
    (A + Real.sqrt (A^2 + 4)) / 2 < A + 1 :=
  paper_metallic_compression_extremum_seeds hA

set_option maxHeartbeats 400000 in
/-- At the metallic-compression extremum `A = 3 / 2`, the Perron root locks to `2`, and the
    compression slope takes the closed form `log (5 / 4)`.
    cor:metallic-compression-locking-lambda2 -/
theorem paper_metallic_compression_locking_lambda2 :
    ((3 / 2 : ℝ) + Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4)) / 2 = 2 ∧
      Real.log (((3 / 2 : ℝ) + 1) / (((3 / 2 : ℝ) + Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4)) / 2)) =
        Real.log (5 / 4) := by
  have hsqrt : Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4) = 5 / 2 := by
    have hnonneg : (0 : ℝ) ≤ 5 / 2 := by positivity
    rw [show (((3 / 2 : ℝ) ^ 2) + 4) = (5 / 2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq hnonneg]
  have hlambda : ((3 / 2 : ℝ) + Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4)) / 2 = 2 := by
    calc
      ((3 / 2 : ℝ) + Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4)) / 2
          = ((3 / 2 : ℝ) + 5 / 2) / 2 := by rw [hsqrt]
      _ = 2 := by norm_num
  constructor
  · exact hlambda
  · calc
      Real.log (((3 / 2 : ℝ) + 1) / (((3 / 2 : ℝ) + Real.sqrt (((3 / 2 : ℝ) ^ 2) + 4)) / 2))
          = Real.log (((3 / 2 : ℝ) + 1) / 2) := by rw [hlambda]
      _ = Real.log (5 / 4) := by norm_num

end Omega.Folding.MetallicCompressionExtremum
