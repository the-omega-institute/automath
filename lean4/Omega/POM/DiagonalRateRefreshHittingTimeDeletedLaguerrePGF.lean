import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingSetHitAndOccupancy
import Omega.POM.DiagonalRateDiagonalClosureRankone
import Omega.POM.DiagonalRateRefreshHittingTimePGFClosed

namespace Omega.POM

/-- Singleton-deleted Laguerre closed form for the diagonal refresh hitting-time PGF. -/
def pom_diagonal_rate_refresh_hitting_time_deleted_laguerre_pgf_formula {α : Type*}
    [Fintype α] [DecidableEq α] (κ : ℚ) (t : α → ℚ) (x y : α) (s : ℚ) : Prop :=
  diagonalRateAbsorbingSetHitPGF κ s t (fun z => 1 / (t z - κ)) ({y} : Finset α) x =
    s * κ * (t x - κ) / (t y - κ) *
      diagonalRateDeletedSetMinorProduct ({y} : Finset α) x t (κ * s) /
        diagonalRateDeletedSetLaguerreDenominator κ ({y} : Finset α) t (κ * s)

/-- Paper label: `thm:pom-diagonal-rate-refresh-hitting-time-deleted-laguerre-pgf`. The
singleton-deleted refresh hitting-time PGF is the corresponding deleted-set closed form specialized
to `π(z) = 1 / (t z - κ)`, with the singleton deleted mass reduced to `1 / (t y - κ)`. -/
theorem paper_pom_diagonal_rate_refresh_hitting_time_deleted_laguerre_pgf
    {α : Type*} [Fintype α] [DecidableEq α] (κ : ℚ) (t : α → ℚ) (x y : α) (s : ℚ) :
    pom_diagonal_rate_refresh_hitting_time_deleted_laguerre_pgf_formula κ t x y s := by
  simp [pom_diagonal_rate_refresh_hitting_time_deleted_laguerre_pgf_formula,
    diagonalRateAbsorbingSetHitPGF, diagonalRateDeletedSetMass, div_eq_mul_inv]
  left
  left
  ac_rfl

end Omega.POM
