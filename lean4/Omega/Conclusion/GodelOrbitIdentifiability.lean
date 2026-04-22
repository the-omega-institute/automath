import Mathlib.Tactic
import Omega.Conclusion.PrimeRegisterGodelOrbitSuperexpLoglaw

namespace Omega.Conclusion

open PrimeRegisterGodelOrbitSuperexpLoglawData

/-- Paper label: `cor:conclusion-godel-orbit-identifiability`. The packaged superexponential
log-law already isolates the main term and the weighted correction, so the orbit-count identity
and the normalized error term follow directly. -/
def paper_conclusion_godel_orbit_identifiability
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) : Prop :=
  D.superexpLogAsymptotic ∧
    (D.prime_register_godel_orbit_superexp_loglaw_logOrbitCount -
        D.prime_register_godel_orbit_superexp_loglaw_mainTerm =
      D.prime_register_godel_orbit_superexp_loglaw_scale *
        D.prime_register_godel_orbit_superexp_loglaw_orbitExpectation) ∧
    (D.prime_register_godel_orbit_superexp_loglaw_logOrbitCount =
      D.prime_register_godel_orbit_superexp_loglaw_scale *
        (Real.log D.n + Real.log (Real.log D.n) + Real.log D.mu +
          D.prime_register_godel_orbit_superexp_loglaw_orbitExpectation))

theorem conclusion_godel_orbit_identifiability_holds
    (D : PrimeRegisterGodelOrbitSuperexpLoglawData) :
    paper_conclusion_godel_orbit_identifiability D := by
  have hloglaw := paper_conclusion_prime_register_godel_orbit_superexp_loglaw D
  refine ⟨hloglaw, ?_, hloglaw.2⟩
  unfold PrimeRegisterGodelOrbitSuperexpLoglawData.prime_register_godel_orbit_superexp_loglaw_logOrbitCount
  unfold PrimeRegisterGodelOrbitSuperexpLoglawData.prime_register_godel_orbit_superexp_loglaw_mainTerm
  ring

end Omega.Conclusion
