import Mathlib.Tactic
import Omega.Folding.KilloPrimeFreedomNonFinitizability

namespace Omega.Zeta

/-- Concrete rank parameter for a finite Grothendieck-completion target. -/
structure xi_time_part62ca_no_multiplicative_embedding_into_finite_grothendieck_rank_data where
  rank : ℕ

/-- The first `rank + 1` prime directions cannot inject linearly into `rank` rational coordinates. -/
def xi_time_part62ca_no_multiplicative_embedding_into_finite_grothendieck_rank_statement
    (D : xi_time_part62ca_no_multiplicative_embedding_into_finite_grothendieck_rank_data) :
    Prop :=
  Omega.Folding.killoFiniteRegisterLinearizationObstructed D.rank

/-- Paper label:
`thm:xi-time-part62ca-no-multiplicative-embedding-into-finite-grothendieck-rank`. -/
theorem paper_xi_time_part62ca_no_multiplicative_embedding_into_finite_grothendieck_rank
    (D : xi_time_part62ca_no_multiplicative_embedding_into_finite_grothendieck_rank_data) :
    xi_time_part62ca_no_multiplicative_embedding_into_finite_grothendieck_rank_statement D := by
  exact (Omega.Folding.paper_killo_prime_freedom_non_finitizability).2 D.rank

end Omega.Zeta
