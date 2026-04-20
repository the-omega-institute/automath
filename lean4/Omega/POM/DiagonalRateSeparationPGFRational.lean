import Omega.POM.DiagonalRateAcceptRefreshSeparationExact
import Omega.POM.DiagonalRateAcceptRefreshSSTPGF

namespace Omega.POM

/-- Publication-facing corollary packaging the rationality transfer for the diagonal-rate
separation PGF together with the resulting numerator-degree bound.
    cor:pom-diagonal-rate-separation-pgf-rational -/
theorem paper_pom_diagonal_rate_separation_pgf_rational
    (separationExact sstPgf separationPgfRational numeratorDegreeBound : Prop)
    (hExact : separationExact) (hPgf : sstPgf)
    (hTransfer : separationExact -> sstPgf -> separationPgfRational)
    (hDegree : separationPgfRational -> numeratorDegreeBound) :
    separationPgfRational ∧ numeratorDegreeBound := by
  have hRational : separationPgfRational := hTransfer hExact hPgf
  exact ⟨hRational, hDegree hRational⟩

end Omega.POM
