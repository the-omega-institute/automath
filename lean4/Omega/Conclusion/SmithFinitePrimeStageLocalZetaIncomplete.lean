import Mathlib.Tactic
import Omega.Zeta.CyclicLiftFiniteProbeEvasion

namespace Omega.Conclusion

open Omega.Zeta

/-- Concrete finite-prime audit data for local-zeta Smith completion tests. -/
structure conclusion_smith_finite_prime_stage_local_zeta_incomplete_data where
  auditedPrimes : Finset ℕ

namespace conclusion_smith_finite_prime_stage_local_zeta_incomplete_data

/-- Smith completions that avoid every nontrivial modulus visible to the finite local-zeta audit. -/
def conclusion_smith_finite_prime_stage_local_zeta_incomplete_smith_completion_candidates
    (D : conclusion_smith_finite_prime_stage_local_zeta_incomplete_data) : Set ℕ :=
  {q : ℕ | Nat.Prime q ∧ ∀ p ∈ D.auditedPrimes, 2 ≤ p → q % p ≠ 0}

/-- The finite prime-stage local-zeta audit misses a completion beyond its finite ledger. -/
def finitePrimeAuditIncomplete
    (D : conclusion_smith_finite_prime_stage_local_zeta_incomplete_data) : Prop :=
  ∃ q ∈ D.conclusion_smith_finite_prime_stage_local_zeta_incomplete_smith_completion_candidates,
    D.auditedPrimes.sum id < q

/-- There are infinitely many pairwise distinct Smith completions invisible to the finite audit. -/
def infinitelyManySmithCompletions
    (D : conclusion_smith_finite_prime_stage_local_zeta_incomplete_data) : Prop :=
  Set.Infinite
    D.conclusion_smith_finite_prime_stage_local_zeta_incomplete_smith_completion_candidates

end conclusion_smith_finite_prime_stage_local_zeta_incomplete_data

open conclusion_smith_finite_prime_stage_local_zeta_incomplete_data

/-- Paper label: `cor:conclusion-smith-finite-prime-stage-local-zeta-incomplete`. -/
theorem paper_conclusion_smith_finite_prime_stage_local_zeta_incomplete
    (D : conclusion_smith_finite_prime_stage_local_zeta_incomplete_data) :
    D.finitePrimeAuditIncomplete ∧ D.infinitelyManySmithCompletions := by
  have hinf :
      Set.Infinite
        D.conclusion_smith_finite_prime_stage_local_zeta_incomplete_smith_completion_candidates := by
    simpa [conclusion_smith_finite_prime_stage_local_zeta_incomplete_smith_completion_candidates] using
      paper_zeta_cyclic_lift_finite_probe_evasion D.auditedPrimes
  refine ⟨?_, hinf⟩
  rw [Set.infinite_iff_exists_gt] at hinf
  rcases hinf (D.auditedPrimes.sum id) with ⟨q, hqmem, hqgt⟩
  exact ⟨q, hqmem, hqgt⟩

end Omega.Conclusion
