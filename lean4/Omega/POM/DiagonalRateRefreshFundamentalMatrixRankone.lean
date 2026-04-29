import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingSetHitAndOccupancy

namespace Omega.POM

/-- Singleton-deleted rank-one formula for the diagonal refresh fundamental matrix. -/
def pom_diagonal_rate_refresh_fundamental_matrix_rankone_formula {α : Type*}
    [Fintype α] [DecidableEq α] (r π : α → ℚ) (y : α) : Prop :=
  ∀ x z,
    diagonalRateAbsorbingSetFundamentalMatrixEntry r π ({y} : Finset α) x z =
      (if x = z then 1 / r x else 0) + π z / (π y * r z)

/-- Paper label: `thm:pom-diagonal-rate-refresh-fundamental-matrix-rankone`. The singleton-deleted
rank-one refresh fundamental matrix is the deleted-set closed form with `π({y}) = π(y)`. -/
theorem paper_pom_diagonal_rate_refresh_fundamental_matrix_rankone
    {α : Type*} [Fintype α] [DecidableEq α] (r π : α → ℚ) (y : α) :
    pom_diagonal_rate_refresh_fundamental_matrix_rankone_formula r π y := by
  intro x z
  simp [diagonalRateAbsorbingSetFundamentalMatrixEntry, diagonalRateDeletedSetMass]

end Omega.POM
