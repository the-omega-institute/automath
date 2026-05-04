import Omega.Conclusion.PrimeRegisterFixed2adicAmbientVsFiniteLedger
import Omega.Conclusion.StableMultiplicationFiniteRankLedgerImpossibility

namespace Omega.Conclusion

/-- A concrete two-event alphabet encoded in base `2`. -/
abbrev conclusion_prime_register_ranktwo_host_nonobstruction_eventAlphabet :=
  Fin 2

/-- Length-two base-`2` event streams, represented by their four possible addresses. -/
abbrev conclusion_prime_register_ranktwo_host_nonobstruction_eventStream :=
  Fin 4

/-- Base-`2` encoding of a finite event stream. -/
def conclusion_prime_register_ranktwo_host_nonobstruction_eventEncoding
    (s : conclusion_prime_register_ranktwo_host_nonobstruction_eventStream) : ℕ :=
  s.1

private lemma conclusion_prime_register_ranktwo_host_nonobstruction_eventEncoding_injective :
    Function.Injective conclusion_prime_register_ranktwo_host_nonobstruction_eventEncoding := by
  intro s t h
  exact Fin.ext h

/-- Paper-facing package for the rank-two host non-obstruction theorem: the fixed rank-two
ambient is faithful, the finite base-`B` stream interface is injective on its symbolic image, and
finite additive ledgers cannot faithfully linearize the multiplicative prime-register semantics. -/
def conclusion_prime_register_ranktwo_host_nonobstruction_package : Prop :=
  Fintype.card (Fin 2) = 2 ∧
    Function.Injective primeRegisterAffineAction ∧
    Function.Injective conclusion_prime_register_ranktwo_host_nonobstruction_eventEncoding ∧
    conclusion_stable_multiplication_finite_rank_ledger_impossibility_statement

/-- Paper label: `thm:conclusion-prime-register-ranktwo-host-nonobstruction`. -/
theorem paper_conclusion_prime_register_ranktwo_host_nonobstruction :
    conclusion_prime_register_ranktwo_host_nonobstruction_package := by
  have hPrime := paper_conclusion_prime_register_fixed_2adic_ambient_vs_finite_ledger
  have hLedger := paper_conclusion_stable_multiplication_finite_rank_ledger_impossibility
  exact
    ⟨hPrime.1, hPrime.2.1,
      conclusion_prime_register_ranktwo_host_nonobstruction_eventEncoding_injective, hLedger⟩

end Omega.Conclusion
