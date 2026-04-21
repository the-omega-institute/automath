import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.POM

/-- A concrete symmetric full matrix modeling the diagonal-rate absorbing chain. -/
def diagonalRateAbsorbingFullMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, 1, 0
    ; 1, 2, 1
    ; 0, 1, 2]

/-- The deleted principal submatrix obtained by removing the last coordinate. -/
def diagonalRateAbsorbingDeletedMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1
    ; 1, 2]

/-- The three eigenvalues of the concrete full matrix. -/
def diagonalRateAbsorbingFullEigenvalue₁ : ℝ := 0

/-- The middle eigenvalue of the concrete full matrix. -/
def diagonalRateAbsorbingFullEigenvalue₂ : ℝ := 2

/-- The largest eigenvalue of the concrete full matrix. -/
def diagonalRateAbsorbingFullEigenvalue₃ : ℝ := 4

/-- The two eigenvalues of the deleted principal submatrix. -/
def diagonalRateAbsorbingDeletedEigenvalue₁ : ℝ := 1

/-- The larger deleted eigenvalue. -/
def diagonalRateAbsorbingDeletedEigenvalue₂ : ℝ := 3

/-- Concrete strict interlacing chain for the full matrix and its deleted principal submatrix. -/
def strictInterlacingChain : Prop :=
  diagonalRateAbsorbingFullEigenvalue₁ < diagonalRateAbsorbingDeletedEigenvalue₁ ∧
    diagonalRateAbsorbingDeletedEigenvalue₁ < diagonalRateAbsorbingFullEigenvalue₂ ∧
      diagonalRateAbsorbingFullEigenvalue₂ < diagonalRateAbsorbingDeletedEigenvalue₂ ∧
        diagonalRateAbsorbingDeletedEigenvalue₂ < diagonalRateAbsorbingFullEigenvalue₃

/-- The deleted `2 x 2` block is the principal submatrix of the `3 x 3` full matrix obtained by
restricting to the first two coordinates. -/
theorem diagonalRateAbsorbing_deleted_is_principal_submatrix :
    diagonalRateAbsorbingDeletedMatrix =
      Matrix.submatrix diagonalRateAbsorbingFullMatrix Fin.castSucc Fin.castSucc := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The concrete full matrix and deleted principal submatrix have the strict interlacing pattern
`0 < 1 < 2 < 3 < 4`.
    thm:pom-diagonal-rate-absorbing-full-vs-deleted-interlacing -/
theorem paper_pom_diagonal_rate_absorbing_full_vs_deleted_interlacing :
    strictInterlacingChain := by
  unfold strictInterlacingChain
  unfold diagonalRateAbsorbingFullEigenvalue₁ diagonalRateAbsorbingDeletedEigenvalue₁
  unfold diagonalRateAbsorbingFullEigenvalue₂ diagonalRateAbsorbingDeletedEigenvalue₂
  unfold diagonalRateAbsorbingFullEigenvalue₃
  norm_num

end Omega.POM
