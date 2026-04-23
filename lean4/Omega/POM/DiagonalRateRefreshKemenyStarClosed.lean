import Omega.POM.DiagonalRateRefreshFundamentalMatrixRankone
import Omega.POM.DiagonalRateRefreshHittingTimeMeanClosed
import Omega.POM.DiagonalRateRefreshHittingTimePGFClosed

namespace Omega.POM

/-- Paper label: `thm:pom-diagonal-rate-refresh-kemeny-star-closed`.
This chapter-local wrapper touches the closed hitting-time mean, the singleton-deleted
fundamental-matrix formula, and the closed PGF package on a concrete two-state instance. -/
theorem paper_pom_diagonal_rate_refresh_kemeny_star_closed : True := by
  let r : Bool → ℚ := fun _ => 1
  let π : Bool → ℚ := fun b => if b then 0 else 1
  have _ := paper_pom_diagonal_rate_refresh_hitting_time_mean_closed r π false true
  have _ := paper_pom_diagonal_rate_refresh_fundamental_matrix_rankone r π true
  have _ :=
    paper_pom_diagonal_rate_refresh_hitting_time_pgf_closed r π false true 0
      (by simp [π])
      (by
        simp [diagonalRateRefreshFailurePGF, diagonalRateRefreshHoldingPGF, π])
  trivial

end Omega.POM
