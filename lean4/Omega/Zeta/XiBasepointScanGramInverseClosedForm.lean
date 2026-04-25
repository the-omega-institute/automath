import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Omega.Zeta.XiBasepointScanFullRankWeightGaugeInvariance

namespace Omega.Zeta

open Matrix

/-- Paper label: `prop:xi-basepoint-scan-gram-inverse-closed-form`.

In the full-rank anchor chart, the weighted feature matrix factors as the unweighted Cauchy
matrix times the square-root weight diagonal. The inverse Gram matrix is consequently the
transpose-inverse times the inverse of the feature matrix, and its entries expand as the finite
matrix product. -/
theorem paper_xi_basepoint_scan_gram_inverse_closed_form {kappa : ℕ}
    (D : XiBasepointAnchorData kappa kappa)
    (hdet : D.anchorFrame.det ≠ 0)
    (hwt : ∀ j, 0 < D.weights j) :
    D.anchorFrame = D.anchorCauchyMatrix * xiBasepointWeightSqrtDiag D ∧
      D.anchorFrame⁻¹ = (xiBasepointWeightSqrtDiag D)⁻¹ * D.anchorCauchyMatrix⁻¹ ∧
      D.anchorGram⁻¹ = D.anchorFrame.transpose⁻¹ * D.anchorFrame⁻¹ ∧
      ∀ i j,
        D.anchorGram⁻¹ i j =
          ∑ k, D.anchorFrame.transpose⁻¹ i k * D.anchorFrame⁻¹ k j := by
  let C : Matrix (Fin kappa) (Fin kappa) ℂ := D.anchorCauchyMatrix
  let W : Matrix (Fin kappa) (Fin kappa) ℂ := xiBasepointWeightSqrtDiag D
  let V : Matrix (Fin kappa) (Fin kappa) ℂ := D.anchorFrame
  have hV : V = C * W := by
    simpa [V, C, W] using xiBasepoint_anchorFrame_eq_cauchy_mul_weight D
  have hVdet : V.det ≠ 0 := by
    simpa [V] using hdet
  have hVunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hVdet
  have hVtunit : IsUnit V.transpose.det := by
    simpa [Matrix.det_transpose] using hVunit
  have hWdet : W.det ≠ 0 := by
    simpa [W] using xiBasepoint_weight_diag_det_ne_zero D hwt
  have hWunit : IsUnit W.det := isUnit_iff_ne_zero.mpr hWdet
  have hCdet : C.det ≠ 0 := by
    intro hCzero
    apply hVdet
    rw [hV, Matrix.det_mul, hCzero, zero_mul]
  have hCunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hCdet
  have hVInv : V⁻¹ = W⁻¹ * C⁻¹ := by
    have hLeftInv : (W⁻¹ * C⁻¹) * V = 1 := by
      calc
        (W⁻¹ * C⁻¹) * V = W⁻¹ * (C⁻¹ * C) * W := by
          rw [hV]
          simp [Matrix.mul_assoc]
        _ = W⁻¹ * 1 * W := by rw [C.nonsing_inv_mul hCunit]
        _ = 1 := by rw [Matrix.mul_one, W.nonsing_inv_mul hWunit]
    apply Matrix.inv_eq_left_inv
    simpa using hLeftInv
  have hGramInv : D.anchorGram⁻¹ = V.transpose⁻¹ * V⁻¹ := by
    have hRightInv : (V * V.transpose) * (V.transpose⁻¹ * V⁻¹) = 1 := by
      calc
        (V * V.transpose) * (V.transpose⁻¹ * V⁻¹) =
            V * (V.transpose * V.transpose⁻¹) * V⁻¹ := by
          simp [Matrix.mul_assoc]
        _ = V * 1 * V⁻¹ := by rw [V.transpose.mul_nonsing_inv hVtunit]
        _ = 1 := by rw [Matrix.mul_one, V.mul_nonsing_inv hVunit]
    apply Matrix.inv_eq_right_inv
    simpa [XiBasepointAnchorData.anchorGram, V, Matrix.mul_assoc] using hRightInv
  refine ⟨by simpa [V, C, W] using hV, by simpa [V, C, W] using hVInv, ?_, ?_⟩
  · simpa [V] using hGramInv
  · intro i j
    rw [hGramInv]
    simp [Matrix.mul_apply, V]

end Omega.Zeta
