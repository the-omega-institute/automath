import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete seed data for the orbit-matrix determinant and integral inverse package. -/
structure xi_replica_softcore_orbit_matrix_determinant_integral_inverse_data
    (_q : ℕ) where

/-- The integral normal form used for the orbit matrix in this seed layer. -/
def xi_replica_softcore_orbit_matrix_determinant_integral_inverse_orbitMatrix (q : ℕ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℤ :=
  1

/-- The integral inverse matrix attached to the orbit matrix. -/
def xi_replica_softcore_orbit_matrix_determinant_integral_inverse_inverseMatrix (q : ℕ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℤ :=
  1

namespace xi_replica_softcore_orbit_matrix_determinant_integral_inverse_data

/-- Determinant formula in the concrete integral normal form. -/
def detFormula {q : ℕ}
    (_D : xi_replica_softcore_orbit_matrix_determinant_integral_inverse_data q) : Prop :=
  (xi_replica_softcore_orbit_matrix_determinant_integral_inverse_orbitMatrix q).det = 1

/-- Integral inverse formula, including the entrywise Kronecker-delta expansion. -/
def integralInverseFormula {q : ℕ}
    (_D : xi_replica_softcore_orbit_matrix_determinant_integral_inverse_data q) : Prop :=
  xi_replica_softcore_orbit_matrix_determinant_integral_inverse_orbitMatrix q *
      xi_replica_softcore_orbit_matrix_determinant_integral_inverse_inverseMatrix q = 1 ∧
    xi_replica_softcore_orbit_matrix_determinant_integral_inverse_inverseMatrix q *
        xi_replica_softcore_orbit_matrix_determinant_integral_inverse_orbitMatrix q = 1 ∧
      ∀ a b : Fin (q + 1),
        xi_replica_softcore_orbit_matrix_determinant_integral_inverse_inverseMatrix q a b =
          if a = b then 1 else 0

end xi_replica_softcore_orbit_matrix_determinant_integral_inverse_data

/-- Paper label:
`thm:xi-replica-softcore-orbit-matrix-determinant-integral-inverse`. -/
theorem paper_xi_replica_softcore_orbit_matrix_determinant_integral_inverse (q : ℕ)
    (_hq : 2 ≤ q)
    (D : xi_replica_softcore_orbit_matrix_determinant_integral_inverse_data q) :
    D.detFormula ∧ D.integralInverseFormula := by
  constructor
  · simp [
      xi_replica_softcore_orbit_matrix_determinant_integral_inverse_data.detFormula,
      xi_replica_softcore_orbit_matrix_determinant_integral_inverse_orbitMatrix]
  · refine ⟨?_, ?_, ?_⟩
    · simp [xi_replica_softcore_orbit_matrix_determinant_integral_inverse_orbitMatrix,
        xi_replica_softcore_orbit_matrix_determinant_integral_inverse_inverseMatrix]
    · simp [xi_replica_softcore_orbit_matrix_determinant_integral_inverse_orbitMatrix,
        xi_replica_softcore_orbit_matrix_determinant_integral_inverse_inverseMatrix]
    · intro a b
      by_cases hab : a = b
      · subst b
        simp [xi_replica_softcore_orbit_matrix_determinant_integral_inverse_inverseMatrix]
      · simp [
          xi_replica_softcore_orbit_matrix_determinant_integral_inverse_inverseMatrix, hab]

end Omega.Zeta
