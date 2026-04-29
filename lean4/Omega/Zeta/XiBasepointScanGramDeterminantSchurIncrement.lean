import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- The anchor-to-basepoint column in the one-point Gram extension. -/
def xi_basepoint_scan_gram_determinant_schur_increment_scanColumn {κ : ℕ}
    (ξ : Fin κ → ℝ) : Matrix (Fin κ) (Fin 1) ℝ :=
  fun i _ => ξ i

/-- The transpose row of anchor/basepoint inner products. -/
def xi_basepoint_scan_gram_determinant_schur_increment_scanRow {κ : ℕ}
    (ξ : Fin κ → ℝ) : Matrix (Fin 1) (Fin κ) ℝ :=
  fun _ i => ξ i

/-- The scalar Gram entry of the new basepoint: anchor energy plus orthogonal residual energy. -/
def xi_basepoint_scan_gram_determinant_schur_increment_scanScalar {κ : ℕ}
    (ξ : Fin κ → ℝ) (r : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => (∑ i : Fin κ, (ξ i) ^ (2 : ℕ)) + r ^ (2 : ℕ)

/-- The full block Gram matrix obtained by adjoining one basepoint to an orthonormal anchor block. -/
def xi_basepoint_scan_gram_determinant_schur_increment_gramExtension {κ : ℕ}
    (ξ : Fin κ → ℝ) (r : ℝ) : Matrix (Sum (Fin κ) (Fin 1)) (Sum (Fin κ) (Fin 1)) ℝ :=
  Matrix.fromBlocks 1
    (xi_basepoint_scan_gram_determinant_schur_increment_scanColumn ξ)
    (xi_basepoint_scan_gram_determinant_schur_increment_scanRow ξ)
    (xi_basepoint_scan_gram_determinant_schur_increment_scanScalar ξ r)

/-- The residual vector after orthogonal projection onto the anchor span leaves only the new
orthogonal coordinate. -/
def xi_basepoint_scan_gram_determinant_schur_increment_residualVector
    (r : ℝ) : Fin 1 → ℝ :=
  fun _ => r

/-- Squared norm of the residual after orthogonal projection onto the anchor span. -/
def xi_basepoint_scan_gram_determinant_schur_increment_residualNormSq (r : ℝ) : ℝ :=
  ∑ i : Fin 1, (xi_basepoint_scan_gram_determinant_schur_increment_residualVector r i) ^ (2 : ℕ)

lemma xi_basepoint_scan_gram_determinant_schur_increment_residualNormSq_eq (r : ℝ) :
    xi_basepoint_scan_gram_determinant_schur_increment_residualNormSq r = r ^ (2 : ℕ) := by
  simp [xi_basepoint_scan_gram_determinant_schur_increment_residualNormSq,
    xi_basepoint_scan_gram_determinant_schur_increment_residualVector]

lemma xi_basepoint_scan_gram_determinant_schur_increment_gap_formula {κ : ℕ}
    (ξ : Fin κ → ℝ) (r : ℝ) :
    Matrix.det
        (xi_basepoint_scan_gram_determinant_schur_increment_scanScalar ξ r -
          xi_basepoint_scan_gram_determinant_schur_increment_scanRow ξ *
            xi_basepoint_scan_gram_determinant_schur_increment_scanColumn ξ) =
      xi_basepoint_scan_gram_determinant_schur_increment_residualNormSq r := by
  rw [xi_basepoint_scan_gram_determinant_schur_increment_residualNormSq_eq]
  have hsq : ∑ i : Fin κ, ξ i ^ (2 : ℕ) = ∑ i : Fin κ, ξ i * ξ i := by
    simp [pow_two]
  simp [xi_basepoint_scan_gram_determinant_schur_increment_scanScalar,
    xi_basepoint_scan_gram_determinant_schur_increment_scanRow,
    xi_basepoint_scan_gram_determinant_schur_increment_scanColumn, Matrix.mul_apply, hsq]

/-- Paper label: `prop:xi-basepoint-scan-gram-determinant-schur-increment`. With an orthonormal
anchor block, the determinant increment for adjoining one point is exactly the determinant of the
scalar Schur complement, and that complement is the squared norm of the residual left after
orthogonal projection onto the anchor span. -/
theorem paper_xi_basepoint_scan_gram_determinant_schur_increment {κ : ℕ}
    (ξ : Fin κ → ℝ) (r : ℝ) :
    Matrix.det
        (xi_basepoint_scan_gram_determinant_schur_increment_gramExtension ξ r) =
      Matrix.det
        (xi_basepoint_scan_gram_determinant_schur_increment_scanScalar ξ r -
          xi_basepoint_scan_gram_determinant_schur_increment_scanRow ξ *
            xi_basepoint_scan_gram_determinant_schur_increment_scanColumn ξ) ∧
    Matrix.det
        (xi_basepoint_scan_gram_determinant_schur_increment_scanScalar ξ r -
          xi_basepoint_scan_gram_determinant_schur_increment_scanRow ξ *
            xi_basepoint_scan_gram_determinant_schur_increment_scanColumn ξ) =
      xi_basepoint_scan_gram_determinant_schur_increment_residualNormSq r := by
  refine ⟨?_, xi_basepoint_scan_gram_determinant_schur_increment_gap_formula ξ r⟩
  exact by
    simpa [xi_basepoint_scan_gram_determinant_schur_increment_gramExtension] using
      (Matrix.det_fromBlocks_one₁₁
        (xi_basepoint_scan_gram_determinant_schur_increment_scanColumn ξ)
        (xi_basepoint_scan_gram_determinant_schur_increment_scanRow ξ)
        (xi_basepoint_scan_gram_determinant_schur_increment_scanScalar ξ r))

end Omega.Zeta
