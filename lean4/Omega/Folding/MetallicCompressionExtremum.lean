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

end Omega.Folding.MetallicCompressionExtremum
