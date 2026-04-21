import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Omega.Zeta.XiBasepointScanAnchorDetCauchyVandermonde

namespace Omega.Zeta

open Matrix

/-- Concrete full-rank anchor data for the kernel-completeness identity. The only extra input
beyond the existing anchor frame is the non-vanishing of its determinant. -/
structure XiBasepointScanKernelCompletenessData where
  kappa : ℕ
  anchorData : XiBasepointAnchorData kappa kappa
  frameDetNeZero : anchorData.anchorFrame.det ≠ 0

/-- The anchor Gram matrix is invertible when its determinant is nonzero. -/
def XiBasepointScanKernelCompletenessData.gramInvertible
    (D : XiBasepointScanKernelCompletenessData) : Prop :=
  D.anchorData.anchorGram.det ≠ 0

/-- The full-rank anchor frame reconstructs the identity after sandwiching the Gram inverse
between the feature matrix and its transpose. -/
def XiBasepointScanKernelCompletenessData.kernelReconstruction
    (D : XiBasepointScanKernelCompletenessData) : Prop :=
  D.anchorData.anchorFrame.transpose * D.anchorData.anchorGram⁻¹ * D.anchorData.anchorFrame = 1

/-- `prop:xi-basepoint-scan-kernel-completeness-full-rank` -/
theorem paper_xi_basepoint_scan_kernel_completeness_full_rank
    (D : XiBasepointScanKernelCompletenessData) : D.gramInvertible ∧ D.kernelReconstruction := by
  let V : Matrix (Fin D.kappa) (Fin D.kappa) ℂ := D.anchorData.anchorFrame
  have hVdet : V.det ≠ 0 := by
    simpa [V] using D.frameDetNeZero
  have hVunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hVdet
  have hVtunit : IsUnit V.transpose.det := by
    simpa [Matrix.det_transpose] using hVunit
  have hGram : D.anchorData.anchorGram = V * V.transpose := by
    rfl
  have hGramDet : D.anchorData.anchorGram.det ≠ 0 := by
    rw [hGram, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hVdet hVdet
  have hGramInv : D.anchorData.anchorGram⁻¹ = V.transpose⁻¹ * V⁻¹ := by
    have hRightInv : (V * V.transpose) * (V.transpose⁻¹ * V⁻¹) = 1 := by
      calc
        (V * V.transpose) * (V.transpose⁻¹ * V⁻¹) = V * (V.transpose * V.transpose⁻¹) * V⁻¹ := by
          simp [Matrix.mul_assoc]
        _ = V * 1 * V⁻¹ := by rw [V.transpose.mul_nonsing_inv hVtunit]
        _ = 1 := by rw [Matrix.mul_one, V.mul_nonsing_inv hVunit]
    apply Matrix.inv_eq_right_inv
    simpa [hGram, Matrix.mul_assoc] using hRightInv
  refine ⟨hGramDet, ?_⟩
  rw [XiBasepointScanKernelCompletenessData.kernelReconstruction, hGramInv]
  calc
    D.anchorData.anchorFrame.transpose * (V.transpose⁻¹ * V⁻¹) * D.anchorData.anchorFrame =
        (V.transpose * V.transpose⁻¹) * (V⁻¹ * V) := by
          simp [V, Matrix.mul_assoc]
    _ = 1 := by
      rw [V.transpose.mul_nonsing_inv hVtunit, V.nonsing_inv_mul hVunit]
      simp

end Omega.Zeta
