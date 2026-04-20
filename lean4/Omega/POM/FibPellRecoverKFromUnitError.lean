import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.FibPellQuadratic

namespace Omega.POM

/-- Paper label: `cor:pom-recover-k-from-unit-error`. The exact Fibonacci unit error
`|F_{k+1} - F_k φ| = φ⁻ᵏ` lets us recover `k` by taking a logarithm base `φ`. -/
theorem paper_pom_recover_k_from_unit_error (k : ℕ) :
    -Real.log |((Nat.fib (k + 1) : ℝ) - (Nat.fib k : ℝ) * Real.goldenRatio)| /
        Real.log Real.goldenRatio =
      k := by
  rcases Omega.POM.FibPellQuadratic.paper_pom_zphi_unit_certificate_error k with ⟨herr, _⟩
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hlogphi_pos : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have hinv_nonneg : 0 ≤ (Real.goldenRatio⁻¹ : ℝ) := by positivity
  have habs :
      |((Nat.fib (k + 1) : ℝ) - (Nat.fib k : ℝ) * Real.goldenRatio)| =
        (Real.goldenRatio⁻¹ : ℝ) ^ k := by
    rw [herr, abs_mul]
    rw [abs_of_nonneg (pow_nonneg hinv_nonneg _)]
    simp
  calc
    -Real.log |((Nat.fib (k + 1) : ℝ) - (Nat.fib k : ℝ) * Real.goldenRatio)| /
        Real.log Real.goldenRatio
      = -Real.log ((Real.goldenRatio⁻¹ : ℝ) ^ k) / Real.log Real.goldenRatio := by
          rw [habs]
    _ = -(((k : ℝ) * Real.log (Real.goldenRatio⁻¹ : ℝ))) / Real.log Real.goldenRatio := by
          rw [← Real.rpow_natCast, Real.log_rpow (inv_pos.mpr hphi_pos)]
    _ = -(((k : ℝ) * (-Real.log Real.goldenRatio))) / Real.log Real.goldenRatio := by
          rw [Real.log_inv]
    _ = ((k : ℝ) * Real.log Real.goldenRatio) / Real.log Real.goldenRatio := by
          ring
    _ = k := by
          field_simp [ne_of_gt hlogphi_pos]

end Omega.POM
