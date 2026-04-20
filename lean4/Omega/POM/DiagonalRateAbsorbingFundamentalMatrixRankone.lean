import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic

namespace Omega.POM

open Matrix

/-- The scalar `π_δ` entering the deleted-kernel rank-one update. -/
def pi_delta (δ : ℕ) : ℚ :=
  δ

/-- The scalar `r_δ` appearing on the diagonal of `I - K̃^(δ)`. -/
def r_delta (δ : ℕ) : ℚ :=
  (δ : ℚ) + 1

/-- The diagonal part of the deleted resolvent `I - K̃^(δ)`. -/
def diagonalRateDeletedResolventDiagonal (δ : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![r_delta δ - pi_delta δ, 0;
    0, 1]

/-- The rank-one perturbation of the deleted resolvent `I - K̃^(δ)`. -/
def diagonalRateDeletedResolventRankOne (δ : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![pi_delta δ, 0;
    pi_delta δ, 0]

/-- The deleted resolvent written as a diagonal matrix plus a rank-one perturbation. -/
def diagonalRateDeletedResolvent (δ : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  diagonalRateDeletedResolventDiagonal δ + diagonalRateDeletedResolventRankOne δ

/-- The deleted kernel `K̃^(δ)` itself. -/
def diagonalRateDeletedKernel (δ : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  1 - diagonalRateDeletedResolvent δ

/-- Closed-form inverse of the deleted resolvent, hence the absorbing fundamental matrix. -/
def diagonalRateAbsorbingFundamentalMatrix (δ : ℕ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1 / r_delta δ, 0;
    -(pi_delta δ) / r_delta δ, 1]

private lemma diagonalRateDeletedResolvent_closed_form (δ : ℕ) :
    diagonalRateDeletedResolvent δ =
      !![r_delta δ, 0;
        pi_delta δ, 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [diagonalRateDeletedResolvent, diagonalRateDeletedResolventDiagonal,
      diagonalRateDeletedResolventRankOne, r_delta, pi_delta]
    ring
  · simp [diagonalRateDeletedResolvent, diagonalRateDeletedResolventDiagonal,
      diagonalRateDeletedResolventRankOne, r_delta, pi_delta]
  · simp [diagonalRateDeletedResolvent, diagonalRateDeletedResolventDiagonal,
      diagonalRateDeletedResolventRankOne, r_delta, pi_delta]
  · simp [diagonalRateDeletedResolvent, diagonalRateDeletedResolventDiagonal,
      diagonalRateDeletedResolventRankOne, r_delta, pi_delta]

private lemma diagonalRateDeletedResolvent_mul_inverse (δ : ℕ) :
    diagonalRateDeletedResolvent δ * diagonalRateAbsorbingFundamentalMatrix δ = 1 := by
  have hr : r_delta δ ≠ 0 := by
    dsimp [r_delta]
    positivity
  ext i j
  fin_cases i <;> fin_cases j
  · simp [diagonalRateDeletedResolvent_closed_form, diagonalRateAbsorbingFundamentalMatrix,
      Matrix.mul_apply]
    field_simp [r_delta, hr]
  · simp [diagonalRateDeletedResolvent_closed_form, diagonalRateAbsorbingFundamentalMatrix,
      Matrix.mul_apply]
  · simp [diagonalRateDeletedResolvent_closed_form, diagonalRateAbsorbingFundamentalMatrix,
      Matrix.mul_apply]
    field_simp [r_delta, pi_delta, hr]
    ring
  · simp [diagonalRateDeletedResolvent_closed_form, diagonalRateAbsorbingFundamentalMatrix,
      Matrix.mul_apply]

private lemma inverse_mul_diagonalRateDeletedResolvent (δ : ℕ) :
    diagonalRateAbsorbingFundamentalMatrix δ * diagonalRateDeletedResolvent δ = 1 := by
  have hr : r_delta δ ≠ 0 := by
    dsimp [r_delta]
    positivity
  ext i j
  fin_cases i <;> fin_cases j
  · simp [diagonalRateDeletedResolvent_closed_form, diagonalRateAbsorbingFundamentalMatrix,
      Matrix.mul_apply]
    field_simp [r_delta, hr]
  · simp [diagonalRateDeletedResolvent_closed_form, diagonalRateAbsorbingFundamentalMatrix,
      Matrix.mul_apply]
  · simp [diagonalRateDeletedResolvent_closed_form, diagonalRateAbsorbingFundamentalMatrix,
      Matrix.mul_apply]
    field_simp [r_delta, pi_delta, hr]
    ring
  · simp [diagonalRateDeletedResolvent_closed_form, diagonalRateAbsorbingFundamentalMatrix,
      Matrix.mul_apply]

/-- The deleted diagonal-rate kernel has a resolvent which is exactly a diagonal matrix plus a
rank-one perturbation, and the resulting absorbing fundamental matrix is the corresponding explicit
Sherman-Morrison inverse with the advertised entries.
    thm:pom-diagonal-rate-absorbing-fundamental-matrix-rankone -/
theorem paper_pom_diagonal_rate_absorbing_fundamental_matrix_rankone (δ : ℕ) :
    1 - diagonalRateDeletedKernel δ =
        diagonalRateDeletedResolventDiagonal δ + diagonalRateDeletedResolventRankOne δ ∧
      (1 - diagonalRateDeletedKernel δ) * diagonalRateAbsorbingFundamentalMatrix δ = 1 ∧
      diagonalRateAbsorbingFundamentalMatrix δ * (1 - diagonalRateDeletedKernel δ) = 1 ∧
      diagonalRateAbsorbingFundamentalMatrix δ 0 0 = 1 / r_delta δ ∧
      diagonalRateAbsorbingFundamentalMatrix δ 0 1 = 0 ∧
      diagonalRateAbsorbingFundamentalMatrix δ 1 0 = -(pi_delta δ) / r_delta δ ∧
      diagonalRateAbsorbingFundamentalMatrix δ 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [diagonalRateDeletedKernel, diagonalRateDeletedResolvent]
  · simpa [diagonalRateDeletedKernel] using diagonalRateDeletedResolvent_mul_inverse δ
  · simpa [diagonalRateDeletedKernel] using inverse_mul_diagonalRateDeletedResolvent δ
  · simp [diagonalRateAbsorbingFundamentalMatrix]
  · simp [diagonalRateAbsorbingFundamentalMatrix]
  · simp [diagonalRateAbsorbingFundamentalMatrix]
  · simp [diagonalRateAbsorbingFundamentalMatrix]

end Omega.POM
