import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- Finite atomic moment data for the depth-spectrum Hankel block. The moments are assumed to have
the finite atomic form `μ_n = Σ_j w_j b_j^n`. -/
structure XiFiniteAtomicMomentData (κ : Nat) where
  weights : Fin κ → ℂ
  nodes : Fin κ → ℂ
  moments : Nat → ℂ
  moments_eq : ∀ n : Nat, moments n = ∑ j, weights j * nodes j ^ n

namespace XiFiniteAtomicMomentData

/-- The `κ × κ` Hankel block built from the first `2κ - 1` moments. -/
noncomputable def hankel {κ : Nat} (D : XiFiniteAtomicMomentData κ) :
    Matrix (Fin κ) (Fin κ) ℂ :=
  fun p q => D.moments (p.1 + q.1)

/-- The Vandermonde matrix with row index equal to the power and column index equal to the atom. -/
noncomputable def vandermonde {κ : Nat} (D : XiFiniteAtomicMomentData κ) :
    Matrix (Fin κ) (Fin κ) ℂ :=
  (Matrix.vandermonde D.nodes).transpose

/-- The Hankel block factors through the finite-atomic Vandermonde matrix, and its determinant is
the weight product times the squared Vandermonde factor. -/
def hankelDetFactorsAsVandermondeSquare {κ : Nat} (D : XiFiniteAtomicMomentData κ) : Prop :=
  D.hankel = D.vandermonde * Matrix.diagonal D.weights * D.vandermonde.transpose ∧
    D.hankel.det = (∏ j, D.weights j) * (Matrix.vandermonde D.nodes).det ^ 2

theorem hankel_eq_vandermonde_mul_diagonal_mul_transpose {κ : Nat}
    (D : XiFiniteAtomicMomentData κ) :
    D.hankel = D.vandermonde * Matrix.diagonal D.weights * D.vandermonde.transpose := by
  ext p q
  rw [hankel, D.moments_eq (p.1 + q.1)]
  symm
  calc
    ((D.vandermonde * Matrix.diagonal D.weights) * D.vandermonde.transpose) p q
        = ∑ x, ((D.vandermonde * Matrix.diagonal D.weights) p x) *
            D.vandermonde.transpose x q := by
            simp [Matrix.mul_apply]
    _ = ∑ x, (D.vandermonde p x * D.weights x) * D.vandermonde.transpose x q := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hdiag :
              ∑ j, D.vandermonde p j * Matrix.diagonal D.weights j x =
                D.vandermonde p x * D.weights x := by
            rw [Finset.sum_eq_single x]
            · simp
            · intro j _ hjx
              simp [Matrix.diagonal_apply_ne D.weights hjx]
            · simp
          simp [Matrix.mul_apply, hdiag]
    _ = ∑ x, D.weights x * D.nodes x ^ (p.1 + q.1) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [vandermonde, Matrix.vandermonde_apply, pow_add, mul_assoc, mul_left_comm, mul_comm]

theorem hankel_det_eq_weight_prod_mul_vandermonde_sq {κ : Nat}
    (D : XiFiniteAtomicMomentData κ) :
    D.hankel.det = (∏ j, D.weights j) * (Matrix.vandermonde D.nodes).det ^ 2 := by
  rw [hankel_eq_vandermonde_mul_diagonal_mul_transpose, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_transpose]
  simp [vandermonde, pow_two, mul_assoc, mul_left_comm, mul_comm]

end XiFiniteAtomicMomentData

/-- Paper-facing package: the finite-atomic depth Hankel block is a Vandermonde Gram matrix, and
its determinant factors as the weight product times the squared Vandermonde. -/
theorem paper_xi_depth_hankel_determinant_vandermonde_square (κ : Nat)
    (D : XiFiniteAtomicMomentData κ) : D.hankelDetFactorsAsVandermondeSquare := by
  dsimp [XiFiniteAtomicMomentData.hankelDetFactorsAsVandermondeSquare]
  exact ⟨D.hankel_eq_vandermonde_mul_diagonal_mul_transpose,
    D.hankel_det_eq_weight_prod_mul_vandermonde_sq⟩

end Omega.Zeta
