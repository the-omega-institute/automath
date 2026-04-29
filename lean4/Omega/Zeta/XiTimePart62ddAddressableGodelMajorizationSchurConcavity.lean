import Mathlib.Tactic
import Omega.POM.CoarsegrainingMajorizationSchur

namespace Omega.Zeta

/-- Paper label:
`cor:xi-time-part62dd-addressable-godel-majorization-schur-concavity`. -/
theorem paper_xi_time_part62dd_addressable_godel_majorization_schur_concavity
    (a b logp : ℝ) (hab : b ≤ a) (hb : 0 ≤ b) (hlogp : 0 ≤ logp) :
    logp * Omega.POM.pairTailMass (Omega.POM.coarseFiberPair a b) ≤
      logp * Omega.POM.pairTailMass (Omega.POM.fineFiberPair a b) := by
  have htail :
      Omega.POM.pairTailMass (Omega.POM.coarseFiberPair a b) ≤
        Omega.POM.pairTailMass (Omega.POM.fineFiberPair a b) :=
    (Omega.POM.paper_pom_coarsegraining_majorization_schur a b hab hb).2.2.2
  exact mul_le_mul_of_nonneg_left htail hlogp

end Omega.Zeta
