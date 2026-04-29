import Mathlib.Tactic

namespace Omega.Zeta

/-- The scalar Schur-complement residual of a `2 × 2` block matrix with invertible basepoint. -/
noncomputable def xi_basepoint_scan_gram_plucker_residual_factorization_schurResidual
    (a b c d : ℂ) : ℂ :=
  d - c * a⁻¹ * b

/-- The residual kernel matrix factored through diagonal weights and a frame matrix. -/
noncomputable def xi_basepoint_scan_gram_plucker_residual_factorization_residualMatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (D Q : Matrix n n ℂ) : Matrix n n ℂ :=
  D * Q * Matrix.conjTranspose Q * Matrix.conjTranspose D

/-- Concrete finite-matrix statement package: the `1+1` Schur complement determinant identity
and the determinant factorization of the residual Gram kernel `D Q Qᴴ Dᴴ`. -/
def paper_xi_basepoint_scan_gram_plucker_residual_factorization_statement : Prop :=
  (∀ a b c d : ℂ, a ≠ 0 →
    Matrix.det !![a, b; c, d] =
      a * xi_basepoint_scan_gram_plucker_residual_factorization_schurResidual a b c d) ∧
  (∀ (n : Type*) [Fintype n] [DecidableEq n] (D Q : Matrix n n ℂ),
    Matrix.det
        (xi_basepoint_scan_gram_plucker_residual_factorization_residualMatrix D Q) =
      Matrix.det D * Matrix.det Q * Matrix.det (Matrix.conjTranspose Q) *
        Matrix.det (Matrix.conjTranspose D))

/-- Paper label: `prop:xi-basepoint-scan-gram-plucker-residual-factorization`. -/
theorem paper_xi_basepoint_scan_gram_plucker_residual_factorization :
    paper_xi_basepoint_scan_gram_plucker_residual_factorization_statement := by
  refine ⟨?_, ?_⟩
  · intro a b c d ha
    rw [Matrix.det_fin_two_of]
    unfold xi_basepoint_scan_gram_plucker_residual_factorization_schurResidual
    field_simp [ha]
  · intro n _ _ D Q
    simp [xi_basepoint_scan_gram_plucker_residual_factorization_residualMatrix,
      Matrix.det_mul, mul_assoc]

end Omega.Zeta
