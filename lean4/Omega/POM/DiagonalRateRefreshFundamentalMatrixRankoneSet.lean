import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingSetHitAndOccupancy

namespace Omega.POM

/-- Deleted-set version of the diagonal refresh rank-one fundamental-matrix formula. -/
def pom_diagonal_rate_refresh_fundamental_matrix_rankone_set_formula {α : Type*}
    [Fintype α] [DecidableEq α] (r π : α → ℚ) (B : Finset α) : Prop :=
  ∀ x z, x ∉ B → z ∉ B →
    diagonalRateAbsorbingSetFundamentalMatrixEntry r π B x z =
      (if x = z then 1 / r x else 0) + π z / (diagonalRateDeletedSetMass π B * r z)

/-- Paper label: `prop:pom-diagonal-rate-refresh-fundamental-matrix-rankone-set`.
For a nonempty proper deleted set `B`, the closed-form deleted-set fundamental matrix remains the
same diagonal term plus one rank-one correction, with `π_δ(y)` replaced by `π_δ(B)`. -/
theorem paper_pom_diagonal_rate_refresh_fundamental_matrix_rankone_set
    {α : Type*} [Fintype α] [DecidableEq α] (r π : α → ℚ) (B : Finset α)
    (_hB_nonempty : B.Nonempty) (_hB_proper : B ≠ Finset.univ) :
    pom_diagonal_rate_refresh_fundamental_matrix_rankone_set_formula r π B := by
  intro x z _hx _hz
  rfl

end Omega.POM
