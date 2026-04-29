import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix

/-- Concrete finite-dimensional data for the signed Toeplitz-Hankel determinant split. -/
structure conclusion_visible_toeplitz_determinant_signed_hankel_split_data where
  upperDim : ℕ
  κ : ℕ
  toeplitz :
    Matrix (Sum (Fin upperDim) (Fin κ)) (Sum (Fin upperDim) (Fin κ)) ℝ
  congruence :
    Matrix (Sum (Fin upperDim) (Fin κ)) (Sum (Fin upperDim) (Fin κ)) ℝ
  positiveBlock : Matrix (Fin upperDim) (Fin upperDim) ℝ
  hankelBlock : Matrix (Fin κ) (Fin κ) ℝ
  congruence_diagonalizes :
    congruence.transpose * toeplitz * congruence =
      Matrix.fromBlocks positiveBlock 0 0 (-(hankelBlock.transpose * hankelBlock))
  congruence_det_sq : congruence.det ^ (2 : ℕ) = 1
  positiveBlock_det_pos : 0 < positiveBlock.det
  hankelBlock_det_ne_zero : hankelBlock.det ≠ 0

/-- Exact signed determinant factorization and its sign consequence. -/
def conclusion_visible_toeplitz_determinant_signed_hankel_split_statement
    (D : conclusion_visible_toeplitz_determinant_signed_hankel_split_data) : Prop :=
  D.toeplitz.det =
      (-1 : ℝ) ^ D.κ * D.positiveBlock.det * D.hankelBlock.det ^ (2 : ℕ) ∧
    0 < (-1 : ℝ) ^ D.κ * D.toeplitz.det

private lemma conclusion_visible_toeplitz_determinant_signed_hankel_split_det_congruence
    (D : conclusion_visible_toeplitz_determinant_signed_hankel_split_data) :
    (D.congruence.transpose * D.toeplitz * D.congruence).det =
      D.congruence.det ^ (2 : ℕ) * D.toeplitz.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

private lemma conclusion_visible_toeplitz_determinant_signed_hankel_split_det_block
    (D : conclusion_visible_toeplitz_determinant_signed_hankel_split_data) :
    (Matrix.fromBlocks D.positiveBlock 0 0
        (-(D.hankelBlock.transpose * D.hankelBlock))).det =
      D.positiveBlock.det *
        ((-1 : ℝ) ^ D.κ * D.hankelBlock.det ^ (2 : ℕ)) := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg, Matrix.det_mul, Matrix.det_transpose]
  simp [Fintype.card_fin]
  ring_nf
  exact Or.inl trivial

/-- Paper label: `thm:conclusion-visible-toeplitz-determinant-signed-hankel-split`. -/
theorem paper_conclusion_visible_toeplitz_determinant_signed_hankel_split
    (D : conclusion_visible_toeplitz_determinant_signed_hankel_split_data) :
    conclusion_visible_toeplitz_determinant_signed_hankel_split_statement D := by
  have hdet_diag := congrArg Matrix.det D.congruence_diagonalizes
  have hleft :
      (D.congruence.transpose * D.toeplitz * D.congruence).det =
        D.congruence.det ^ (2 : ℕ) * D.toeplitz.det :=
    conclusion_visible_toeplitz_determinant_signed_hankel_split_det_congruence D
  have hright :
      (Matrix.fromBlocks D.positiveBlock 0 0
          (-(D.hankelBlock.transpose * D.hankelBlock))).det =
        D.positiveBlock.det *
          ((-1 : ℝ) ^ D.κ * D.hankelBlock.det ^ (2 : ℕ)) :=
    conclusion_visible_toeplitz_determinant_signed_hankel_split_det_block D
  have hsplit :
      D.toeplitz.det =
        (-1 : ℝ) ^ D.κ * D.positiveBlock.det * D.hankelBlock.det ^ (2 : ℕ) := by
    have hmain :
        D.congruence.det ^ (2 : ℕ) * D.toeplitz.det =
          D.positiveBlock.det *
            ((-1 : ℝ) ^ D.κ * D.hankelBlock.det ^ (2 : ℕ)) := by
      rw [← hleft, hdet_diag, hright]
    rw [D.congruence_det_sq] at hmain
    nlinarith [hmain]
  refine ⟨hsplit, ?_⟩
  have hprod_pos :
      0 < D.positiveBlock.det * D.hankelBlock.det ^ (2 : ℕ) := by
    exact mul_pos D.positiveBlock_det_pos (sq_pos_of_ne_zero D.hankelBlock_det_ne_zero)
  obtain hsign | hsign := neg_one_pow_eq_or ℝ D.κ
  · rw [hsplit, hsign]
    ring_nf
    exact hprod_pos
  · rw [hsplit, hsign]
    ring_nf
    exact hprod_pos

end Omega.Conclusion
