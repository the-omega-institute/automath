import Omega.POM.DiagonalRateAcceptRefreshSeparationExact

namespace Omega.POM

/-- Paper-facing extraction of the halting-state lemma from the exact accept-refresh package.
    prop:pom-diagonal-rate-accept-refresh-halting-state -/
theorem paper_pom_diagonal_rate_accept_refresh_halting_state
    (D : Omega.POM.DiagonalRateAcceptRefreshSeparationExactData) : D.haltingStateLemma := by
  exact D.haltingStateLemmaWitness

end Omega.POM
