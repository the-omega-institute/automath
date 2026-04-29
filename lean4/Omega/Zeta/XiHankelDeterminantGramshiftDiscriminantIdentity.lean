import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- The Vandermonde matrix appearing in the Gram--shift factorization. -/
noncomputable def xi_hankel_determinant_gramshift_discriminant_identity_vandermonde
    {κ : ℕ} (z : Fin κ → ℂ) : Matrix (Fin κ) (Fin κ) ℂ :=
  (Matrix.vandermonde z).transpose

/-- The diagonal weight matrix in the finite exponential expansion. -/
noncomputable def xi_hankel_determinant_gramshift_discriminant_identity_weight_matrix
    {κ : ℕ} (w : Fin κ → ℂ) : Matrix (Fin κ) (Fin κ) ℂ :=
  Matrix.diagonal w

/-- The `H₀ = (4π) V W Vᵀ` Gram block. -/
noncomputable def xi_hankel_determinant_gramshift_discriminant_identity_h0
    {κ : ℕ} (w : Fin κ → ℂ) (z : Fin κ → ℂ) : Matrix (Fin κ) (Fin κ) ℂ :=
  (4 * Real.pi : ℂ) •
    (xi_hankel_determinant_gramshift_discriminant_identity_vandermonde z *
      xi_hankel_determinant_gramshift_discriminant_identity_weight_matrix w *
        (xi_hankel_determinant_gramshift_discriminant_identity_vandermonde z).transpose)

/-- The unsigned discriminant of the characteristic polynomial, recorded as the squared
Vandermonde determinant. -/
noncomputable def xi_hankel_determinant_gramshift_discriminant_identity_unsigned_discriminant
    {κ : ℕ} (z : Fin κ → ℂ) : ℂ :=
  (xi_hankel_determinant_gramshift_discriminant_identity_vandermonde z).det ^ 2

/-- The product of finite exponential weights. -/
noncomputable def xi_hankel_determinant_gramshift_discriminant_identity_weight_product
    {κ : ℕ} (w : Fin κ → ℂ) : ℂ :=
  ∏ j, w j

/-- Concrete determinant identity obtained from `H₀ = (4π) V W Vᵀ`. -/
def xi_hankel_determinant_gramshift_discriminant_identity_statement : Prop :=
  ∀ (κ : ℕ) (w z : Fin κ → ℂ),
    (xi_hankel_determinant_gramshift_discriminant_identity_h0 w z).det =
      (4 * Real.pi : ℂ) ^ κ *
        xi_hankel_determinant_gramshift_discriminant_identity_weight_product w *
          xi_hankel_determinant_gramshift_discriminant_identity_unsigned_discriminant z

/-- Paper label: `thm:xi-hankel-determinant-gramshift-discriminant-identity`. -/
theorem paper_xi_hankel_determinant_gramshift_discriminant_identity :
    xi_hankel_determinant_gramshift_discriminant_identity_statement := by
  intro κ w z
  unfold xi_hankel_determinant_gramshift_discriminant_identity_h0
    xi_hankel_determinant_gramshift_discriminant_identity_weight_product
    xi_hankel_determinant_gramshift_discriminant_identity_unsigned_discriminant
    xi_hankel_determinant_gramshift_discriminant_identity_weight_matrix
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_transpose]
  simp [xi_hankel_determinant_gramshift_discriminant_identity_vandermonde,
    Fintype.card_fin, pow_two, mul_assoc, mul_left_comm, mul_comm]

end Omega.Zeta
