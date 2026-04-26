import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Scalar Pimsner-Popa witness bound: once the optimal constant is rewritten as `ind⁻¹`, the
witness inequality `(k : ℝ)⁻¹ ≥ λ` forces `k ≤ ind`.
    thm:op-algebra-pimsner-popa-witness-bound -/
theorem paper_op_algebra_pimsner_popa_witness_bound {ind «λ» : ℝ} {k : ℕ} (hInd : 0 < ind)
    (hk : 0 < k) (hLambda : «λ» = ind⁻¹) (hWitness : (k : ℝ)⁻¹ ≥ «λ») :
    «λ» = ind⁻¹ ∧ (k : ℝ) ≤ ind := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  constructor
  · exact hLambda
  · have hInv : ind⁻¹ ≤ (k : ℝ)⁻¹ := by simpa [hLambda] using hWitness
    have hmul :=
      mul_le_mul_of_nonneg_left hInv (show 0 ≤ ind * (k : ℝ) by positivity)
    have hind_ne : ind ≠ 0 := ne_of_gt hInd
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simpa [mul_comm, mul_left_comm, mul_assoc, hind_ne, hk_ne] using hmul

end Omega.OperatorAlgebra
