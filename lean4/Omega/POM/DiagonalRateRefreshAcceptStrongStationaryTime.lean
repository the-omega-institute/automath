import Omega.POM.DiagonalRateAcceptRefreshSSTStrong

namespace Omega.POM

/-- Paper label: `thm:pom-diagonal-rate-refresh-accept-strong-stationary-time`. This is the
paper-facing name for the already verified diagonal accept-refresh strong-stationary-time package.
-/
theorem paper_pom_diagonal_rate_refresh_accept_strong_stationary_time
    (D : DiagonalRateAcceptRefreshSSTStrongData) :
    D.strongStationaryTime ∧ D.stationaryLawAtStop ∧ D.stopLawIndependent := by
  exact paper_pom_diagonal_rate_accept_refresh_sst_strong D

end Omega.POM
