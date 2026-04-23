import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingSetHitAndOccupancy

namespace Omega.POM

/-- Paper label: `thm:pom-diagonal-rate-refresh-hitting-time-deleted-set-laguerre-pgf`.
For the diagonal refresh model, the deleted-set hitting-time PGF is the deleted-set closed form
specialized to the refresh weights `π(z) = 1 / (t z - κ)`. -/
theorem paper_pom_diagonal_rate_refresh_hitting_time_deleted_set_laguerre_pgf
    {α : Type*} [Fintype α] [DecidableEq α]
    (κ : ℚ) (t : α → ℚ) (B : Finset α) (x : α) (s : ℚ) :
    diagonalRateAbsorbingSetHitPGF κ s t (fun z => 1 / (t z - κ)) B x =
      s * κ * diagonalRateDeletedSetMass (fun z => 1 / (t z - κ)) B * (t x - κ) *
        diagonalRateDeletedSetMinorProduct B x t (κ * s) /
          diagonalRateDeletedSetLaguerreDenominator κ B t (κ * s) := by
  rfl

end Omega.POM
