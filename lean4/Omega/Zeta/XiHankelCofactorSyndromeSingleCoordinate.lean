import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The Hankel index `i + j` viewed in `Fin (2 * d + 1)`. -/
def xi_hankel_cofactor_syndrome_single_coordinate_hankel_index (d : Nat)
    (i j : Fin (d + 1)) : Fin (2 * d + 1) :=
  ⟨i.1 + j.1, by
    have hi : i.1 ≤ d := Nat.le_of_lt_succ i.2
    have hj : j.1 ≤ d := Nat.le_of_lt_succ j.2
    omega⟩

/-- The `(d+1) × (d+1)` Hankel block built from `a₀, …, a_{2d}`. -/
def xi_hankel_cofactor_syndrome_single_coordinate_hankel_matrix
    (R : Type*) [CommRing R] (d : Nat) (a : Fin (2 * d + 1) → R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  fun i j => a (xi_hankel_cofactor_syndrome_single_coordinate_hankel_index d i j)

/-- The principal `d × d` Hankel minor obtained by deleting the last row and column. -/
def xi_hankel_cofactor_syndrome_single_coordinate_principal_matrix
    (R : Type*) [CommRing R] (d : Nat) (a : Fin (2 * d + 1) → R) :
    Matrix (Fin d) (Fin d) R :=
  fun i j => a (xi_hankel_cofactor_syndrome_single_coordinate_hankel_index d i.castSucc j.castSucc)

/-- The cofactor column of the last column, represented as the corresponding adjugate column. -/
def xi_hankel_cofactor_syndrome_single_coordinate_cofactor_column
    (R : Type*) [CommRing R] (d : Nat) (a : Fin (2 * d + 1) → R) :
    Fin (d + 1) → R :=
  fun j =>
    (xi_hankel_cofactor_syndrome_single_coordinate_hankel_matrix R d a).adjugate j (Fin.last d)

/-- Concrete package for the last-cofactor Hankel syndrome: when `det H = 0`, the last adjugate
column is a kernel vector, its last coordinate is the principal determinant, and a nonzero
principal determinant forces a nonzero syndrome. -/
def xi_hankel_cofactor_syndrome_single_coordinate_statement
    (R : Type*) [CommRing R] [IsDomain R] (d : Nat) (a : Fin (2 * d + 1) → R) : Prop :=
  let H := xi_hankel_cofactor_syndrome_single_coordinate_hankel_matrix R d a
  let H0 := xi_hankel_cofactor_syndrome_single_coordinate_principal_matrix R d a
  let u := xi_hankel_cofactor_syndrome_single_coordinate_cofactor_column R d a
  H.det = 0 →
    H.mulVec u = 0 ∧
      u (Fin.last d) = H0.det ∧
      (H0.det ≠ 0 → u ≠ 0) ∧
      u (Fin.last d) ∣ H0.det

lemma xi_hankel_cofactor_syndrome_single_coordinate_submatrix_last_last
    (R : Type*) [CommRing R] (d : Nat) (a : Fin (2 * d + 1) → R) :
    (xi_hankel_cofactor_syndrome_single_coordinate_hankel_matrix R d a).submatrix
        (Fin.last d).succAbove (Fin.last d).succAbove =
      xi_hankel_cofactor_syndrome_single_coordinate_principal_matrix R d a := by
  ext i j
  simp [xi_hankel_cofactor_syndrome_single_coordinate_hankel_matrix,
    xi_hankel_cofactor_syndrome_single_coordinate_principal_matrix, Fin.succAbove_last]

/-- Paper label: `thm:xi-hankel-cofactor-syndrome-single-coordinate`. -/
theorem paper_xi_hankel_cofactor_syndrome_single_coordinate
    (R : Type*) [CommRing R] [IsDomain R] (d : Nat) (a : Fin (2 * d + 1) → R) :
    xi_hankel_cofactor_syndrome_single_coordinate_statement R d a := by
  dsimp [xi_hankel_cofactor_syndrome_single_coordinate_statement]
  intro hdet
  let H := xi_hankel_cofactor_syndrome_single_coordinate_hankel_matrix R d a
  let H0 := xi_hankel_cofactor_syndrome_single_coordinate_principal_matrix R d a
  let u := xi_hankel_cofactor_syndrome_single_coordinate_cofactor_column R d a
  have xi_hankel_cofactor_syndrome_single_coordinate_kernel :
      H.mulVec u = 0 := by
    ext i
    simpa [H, u, hdet,
      xi_hankel_cofactor_syndrome_single_coordinate_cofactor_column] using
      congrFun (congrFun (Matrix.mul_adjugate H) i) (Fin.last d)
  have xi_hankel_cofactor_syndrome_single_coordinate_last_coordinate :
      u (Fin.last d) = H0.det := by
    have xi_hankel_cofactor_syndrome_single_coordinate_sign :
        (-1 : R) ^ (↑(Fin.last d) + ↑(Fin.last d) : Nat) = 1 := by
      have hexp : (↑(Fin.last d) + ↑(Fin.last d) : Nat) = 2 * d := by
        have hlast : ((Fin.last d : Fin (d + 1)) : Nat) = d := by
          simpa using (Fin.val_last d)
        calc
          (↑(Fin.last d) + ↑(Fin.last d) : Nat) = d + d := by rw [hlast]
          _ = 2 * d := by omega
      rw [hexp, pow_mul]
      simp
    rw [show u = xi_hankel_cofactor_syndrome_single_coordinate_cofactor_column R d a by rfl]
    rw [show H0 = xi_hankel_cofactor_syndrome_single_coordinate_principal_matrix R d a by rfl]
    rw [xi_hankel_cofactor_syndrome_single_coordinate_cofactor_column,
      Matrix.adjugate_fin_succ_eq_det_submatrix]
    rw [xi_hankel_cofactor_syndrome_single_coordinate_sign, one_mul]
    simpa [H0] using congrArg Matrix.det
      (xi_hankel_cofactor_syndrome_single_coordinate_submatrix_last_last R d a)
  have xi_hankel_cofactor_syndrome_single_coordinate_nonzero :
      H0.det ≠ 0 → u ≠ 0 := by
    intro hH0 hu
    have hu_last := congrFun hu (Fin.last d)
    exact hH0 (by simpa [xi_hankel_cofactor_syndrome_single_coordinate_last_coordinate] using hu_last)
  refine ⟨xi_hankel_cofactor_syndrome_single_coordinate_kernel,
    xi_hankel_cofactor_syndrome_single_coordinate_last_coordinate,
    xi_hankel_cofactor_syndrome_single_coordinate_nonzero, ?_⟩
  exact ⟨1, by
    simpa [mul_comm] using xi_hankel_cofactor_syndrome_single_coordinate_last_coordinate.symm⟩

end Omega.Zeta
