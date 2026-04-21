import Omega.Conclusion.ConnectedToDiscreteConstant
import Omega.Zeta.LocalizedQuotientLedger

namespace Omega.Conclusion

/-- Concrete connected model used for the blind continuous observer on the localized solenoid
shadow. -/
abbrev LocalizedSolenoidObservationModel := ℝ

/-- Prime-probe periodic-point proxy at base `B`: the base support removes primes dividing `B`,
then the solenoid ledger removes the primes in `S`. -/
def solenoidFixedpointPrimeProbe (S : Finset ℕ) (B p : ℕ) : ℕ :=
  Omega.Zeta.localizedIndex S (Omega.Zeta.localizedIndex B.primeFactors p)

/-- Conclusion-level package for the profinite-blindness/fixed-point-ledger dichotomy:
discrete observers on the connected solenoid shadow are constant, while the fixed-base prime probe
still recovers the `B`-outside prime ledger.
    thm:conclusion-solenoid-profinite-blindness-fixedpoint-ledger -/
def SolenoidProfiniteBlindnessFixedpointLedgerStatement : Prop :=
  (∀ {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
      (obs : LocalizedSolenoidObservationModel → F), Continuous obs →
        ∀ x y : LocalizedSolenoidObservationModel, obs x = obs y) ∧
    (∀ (S : Finset ℕ) (B p : ℕ), Nat.Prime p → 2 ≤ B → ¬ p ∣ B →
      ((p ∈ S ↔ solenoidFixedpointPrimeProbe S B p = 1) ∧
        (p ∉ S ↔ solenoidFixedpointPrimeProbe S B p = p)))

theorem paper_conclusion_solenoid_profinite_blindness_fixedpoint_ledger :
    SolenoidProfiniteBlindnessFixedpointLedgerStatement := by
  refine ⟨?_, ?_⟩
  · intro F _ _ obs hobs x y
    exact Omega.Conclusion.ConnectedToDiscreteConstant.continuous_to_discrete_constant
      obs hobs x y
  · intro S B p hp hB hpB
    have hpOutBase : p ∉ B.primeFactors := by
      intro hpMem
      exact hpB (Nat.dvd_of_mem_primeFactors hpMem)
    have hBase : Omega.Zeta.localizedIndex B.primeFactors p = p := by
      simp [Omega.Zeta.localizedIndex, Omega.Zeta.nSperp, hpOutBase]
    constructor
    · simpa [solenoidFixedpointPrimeProbe, hBase] using
        (Omega.Zeta.paper_xi_localized_quotient_index_prime_recovery S hp).1
    · simpa [solenoidFixedpointPrimeProbe, hBase] using
        (Omega.Zeta.paper_xi_localized_quotient_index_prime_recovery S hp).2

end Omega.Conclusion
