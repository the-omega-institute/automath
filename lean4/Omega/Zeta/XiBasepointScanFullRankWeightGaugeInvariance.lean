import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Omega.Zeta.XiBasepointScanAnchorDetCauchyVandermonde

namespace Omega.Zeta

open Matrix

/-- The diagonal matrix carrying the square-root anchor weights. -/
noncomputable def xiBasepointWeightSqrtDiag {kappa : ℕ}
    (D : XiBasepointAnchorData kappa kappa) : Matrix (Fin kappa) (Fin kappa) ℂ :=
  Matrix.diagonal fun j => ((Real.sqrt (D.weights j) : ℝ) : ℂ)

lemma xiBasepoint_anchorFrame_eq_cauchy_mul_weight {kappa : ℕ}
    (D : XiBasepointAnchorData kappa kappa) :
    D.anchorFrame = D.anchorCauchyMatrix * xiBasepointWeightSqrtDiag D := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simpa [mul_comm, XiBasepointAnchorData.anchorFrame, XiBasepointAnchorData.anchorCauchyMatrix,
      xiBasepointWeightSqrtDiag, div_eq_mul_inv]
  · intro x hx hxne
    simp [xiBasepointWeightSqrtDiag, Matrix.diagonal_apply_ne, hxne]
  · intro hj
    exfalso
    exact hj (by simp)

lemma xiBasepoint_weight_diag_det_ne_zero {kappa : ℕ}
    (D : XiBasepointAnchorData kappa kappa) (hwt : ∀ j, 0 < D.weights j) :
    (xiBasepointWeightSqrtDiag D).det ≠ 0 := by
  rw [xiBasepointWeightSqrtDiag, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  exact_mod_cast Real.sqrt_ne_zero'.2 (hwt j)

lemma xiBasepoint_weight_diag_square {kappa : ℕ}
    (D : XiBasepointAnchorData kappa kappa) (hwt : ∀ j, 0 < D.weights j) :
    (xiBasepointWeightSqrtDiag D).det ^ (2 : ℕ) =
      ∏ j, ((D.weights j : ℝ) : ℂ) := by
  rw [xiBasepointWeightSqrtDiag, Matrix.det_diagonal, ← Finset.prod_pow]
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hsqrt : (Real.sqrt (D.weights j)) ^ (2 : ℕ) = D.weights j := by
    rw [pow_two]
    nlinarith [Real.sq_sqrt (le_of_lt (hwt j))]
  exact_mod_cast hsqrt

/-- Paper label: `prop:xi-basepoint-scan-full-rank-weight-gauge-invariance`. -/
theorem paper_xi_basepoint_scan_full_rank_weight_gauge_invariance {kappa : ℕ}
    (D : XiBasepointAnchorData kappa kappa)
    (hdet : D.anchorFrame.det ≠ 0)
    (hwt : ∀ j, 0 < D.weights j) :
    D.anchorFrame.transpose = xiBasepointWeightSqrtDiag D * D.anchorCauchyMatrix.transpose ∧
    D.anchorFrame.transpose⁻¹ =
      D.anchorCauchyMatrix.transpose⁻¹ * (xiBasepointWeightSqrtDiag D)⁻¹ ∧
    D.anchorGram.det =
      ((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ) * D.anchorCauchyMatrix.det ^ (2 : ℕ) := by
  let C : Matrix (Fin kappa) (Fin kappa) ℂ := D.anchorCauchyMatrix
  let W : Matrix (Fin kappa) (Fin kappa) ℂ := xiBasepointWeightSqrtDiag D
  let V : Matrix (Fin kappa) (Fin kappa) ℂ := D.anchorFrame
  have hV : V = C * W := by
    simpa [V, C, W] using xiBasepoint_anchorFrame_eq_cauchy_mul_weight D
  have hVdet : V.det ≠ 0 := by
    simpa [V] using hdet
  have hVunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hVdet
  have hWdet : W.det ≠ 0 := by
    simpa [W] using xiBasepoint_weight_diag_det_ne_zero D hwt
  have hWunit : IsUnit W.det := isUnit_iff_ne_zero.mpr hWdet
  have hCdet : C.det ≠ 0 := by
    intro hCzero
    apply hVdet
    rw [hV, Matrix.det_mul, hCzero, zero_mul]
  have hCunit : IsUnit C.det := isUnit_iff_ne_zero.mpr hCdet
  have hCtunit : IsUnit C.transpose.det := by
    simpa [Matrix.det_transpose] using hCunit
  have hWt : W.transpose = W := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [W, xiBasepointWeightSqrtDiag, Matrix.transpose_apply]
    · have hji : j ≠ i := by
        intro hjiEq
        exact hij hjiEq.symm
      simp [W, xiBasepointWeightSqrtDiag, Matrix.transpose_apply, hij, hji]
  have hVt : V.transpose = W * C.transpose := by
    rw [hV, Matrix.transpose_mul, hWt]
  have hVtInv : V.transpose⁻¹ = C.transpose⁻¹ * W⁻¹ := by
    have hRightInv : (W * C.transpose) * (C.transpose⁻¹ * W⁻¹) = 1 := by
      calc
        (W * C.transpose) * (C.transpose⁻¹ * W⁻¹) = W * (C.transpose * C.transpose⁻¹) * W⁻¹ := by
          simp [Matrix.mul_assoc]
        _ = W * 1 * W⁻¹ := by rw [C.transpose.mul_nonsing_inv hCtunit]
        _ = 1 := by rw [Matrix.mul_one, W.mul_nonsing_inv hWunit]
    apply Matrix.inv_eq_right_inv
    simpa [hVt, Matrix.mul_assoc] using hRightInv
  have hdetFactor :
      D.anchorGram.det = ((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ) * C.det ^ (2 : ℕ) := by
    calc
      D.anchorGram.det = V.det ^ (2 : ℕ) := by
        rw [show D.anchorGram = V * V.transpose by rfl, Matrix.det_mul, Matrix.det_transpose]
        ring
      _ = (C.det * W.det) ^ (2 : ℕ) := by rw [hV, Matrix.det_mul]
      _ = C.det ^ (2 : ℕ) * W.det ^ (2 : ℕ) := by ring
      _ = C.det ^ (2 : ℕ) * ∏ j, ((D.weights j : ℝ) : ℂ) := by
            rw [show W.det ^ (2 : ℕ) = ∏ j, ((D.weights j : ℝ) : ℂ) by
              simpa [W] using xiBasepoint_weight_diag_square D hwt]
      _ = ((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ) * C.det ^ (2 : ℕ) := by ring
  exact ⟨by simpa [V, W, C] using hVt, by simpa [V, W, C] using hVtInv,
    by simpa [C] using hdetFactor⟩

end Omega.Zeta
