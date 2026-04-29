import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix
open scoped BigOperators

/-- Triangular exponent appearing in the product of the shifted Hankel nodes. -/
def conclusion_shifted_hankel_rigidity_tri (q : Nat) : Nat :=
  ∑ k : Fin (q + 1), k.1

/-- The integer node model used for the shifted Hankel determinant. -/
def conclusion_shifted_hankel_rigidity_node (q : Nat) (P : Int) (k : Fin (q + 1)) : Int :=
  P ^ k.1

/-- Vandermonde matrix of the integer node model. -/
noncomputable def conclusion_shifted_hankel_rigidity_vandermonde (q : Nat) (P : Int) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) Int :=
  (Matrix.vandermonde (conclusion_shifted_hankel_rigidity_node q P)).transpose

/-- Diagonal weight matrix for an `r`-shift of the Hankel moments. -/
noncomputable def conclusion_shifted_hankel_rigidity_diagonal (q r : Nat) (P : Int) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) Int :=
  Matrix.diagonal fun k => conclusion_shifted_hankel_rigidity_node q P k ^ r

/-- Shifted Hankel determinant model, written as `V diag(node^r) Vᵀ`. -/
noncomputable def conclusion_shifted_hankel_rigidity_matrix (q r : Nat) (P : Int) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) Int :=
  conclusion_shifted_hankel_rigidity_vandermonde q P *
    conclusion_shifted_hankel_rigidity_diagonal q r P *
      (conclusion_shifted_hankel_rigidity_vandermonde q P).transpose

/-- Determinant of the shifted Hankel model. -/
noncomputable def conclusion_shifted_hankel_rigidity_det (q r : Nat) (P : Int) : Int :=
  Matrix.det (conclusion_shifted_hankel_rigidity_matrix q r P)

lemma conclusion_shifted_hankel_rigidity_prod_nodes (q : Nat) (P : Int) :
    (∏ k : Fin (q + 1), conclusion_shifted_hankel_rigidity_node q P k) =
      P ^ conclusion_shifted_hankel_rigidity_tri q := by
  simpa [conclusion_shifted_hankel_rigidity_node,
    conclusion_shifted_hankel_rigidity_tri] using
    (Finset.prod_pow_eq_pow_sum (s := (Finset.univ : Finset (Fin (q + 1))))
      (f := fun k : Fin (q + 1) => k.1) (a := P))

lemma conclusion_shifted_hankel_rigidity_prod_shift_weights (q r : Nat) (P : Int) :
    (∏ k : Fin (q + 1), conclusion_shifted_hankel_rigidity_node q P k ^ r) =
      P ^ (r * conclusion_shifted_hankel_rigidity_tri q) := by
  calc
    (∏ k : Fin (q + 1), conclusion_shifted_hankel_rigidity_node q P k ^ r) =
        (∏ k : Fin (q + 1), conclusion_shifted_hankel_rigidity_node q P k) ^ r := by
          simpa using
            (Finset.prod_pow (s := (Finset.univ : Finset (Fin (q + 1)))) (n := r)
              (f := conclusion_shifted_hankel_rigidity_node q P))
    _ = (P ^ conclusion_shifted_hankel_rigidity_tri q) ^ r := by
          rw [conclusion_shifted_hankel_rigidity_prod_nodes]
    _ = P ^ (conclusion_shifted_hankel_rigidity_tri q * r) := by
          rw [pow_mul]
    _ = P ^ (r * conclusion_shifted_hankel_rigidity_tri q) := by
          rw [Nat.mul_comm]

lemma conclusion_shifted_hankel_rigidity_det_factor (q r : Nat) (P : Int) :
    conclusion_shifted_hankel_rigidity_det q r P =
      (conclusion_shifted_hankel_rigidity_vandermonde q P).det *
        (∏ k : Fin (q + 1), conclusion_shifted_hankel_rigidity_node q P k ^ r) *
          (conclusion_shifted_hankel_rigidity_vandermonde q P).det := by
  simp [conclusion_shifted_hankel_rigidity_det, conclusion_shifted_hankel_rigidity_matrix,
    conclusion_shifted_hankel_rigidity_diagonal, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_transpose, mul_assoc]

/-- Paper label: `prop:conclusion-shifted-hankel-rigidity`. -/
theorem paper_conclusion_shifted_hankel_rigidity (q r : Nat) (P : Int) :
    conclusion_shifted_hankel_rigidity_det q r P =
      P ^ (r * conclusion_shifted_hankel_rigidity_tri q) *
        conclusion_shifted_hankel_rigidity_det q 0 P := by
  rw [conclusion_shifted_hankel_rigidity_det_factor,
    conclusion_shifted_hankel_rigidity_det_factor,
    conclusion_shifted_hankel_rigidity_prod_shift_weights]
  simp [mul_comm, mul_left_comm]

end Omega.Conclusion
