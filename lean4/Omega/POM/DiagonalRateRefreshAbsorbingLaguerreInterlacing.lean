import Omega.POM.DiagonalRateAbsorbingLaguerreInterlacing

namespace Omega.POM

/-- Paper label: `thm:pom-diagonal-rate-refresh-absorbing-laguerre-interlacing`. In the concrete
toy model already verified for the deleted-point absorbing Laguerre secular equation, the refresh
wrapper inherits the same two interlacing roots and interval-by-interval uniqueness. -/
theorem paper_pom_diagonal_rate_refresh_absorbing_laguerre_interlacing :
    diagonalRateAbsorbingLaguerreInterlacingStatement := by
  simpa using paper_pom_diagonal_rate_absorbing_laguerre_interlacing

end Omega.POM
