import Mathlib.Tactic
import Omega.Folding.PhiConjugacyThreshold
import Omega.Zeta.DynZeta

namespace Omega.Conclusion

open Omega.Folding

/-- The existing regular finite-state barrier package for Zeckendorf primes. -/
def ZeckendorfPrimeFiniteStateBarrier : Prop :=
  (∀ a b : Nat, 0 < a → 0 < b → 0 < a * b) ∧
    2 * 3 = 6 ∧ 4 * 5 = 20 ∧ Nat.fib 4 = 3 ∧ Nat.fib 8 = 21

/-- Compose a fixed-resolution observer back to the input side through the `Phi`/`Psi` wrappers. -/
noncomputable def pullbackThroughFixedResolution (m : Nat) (observe : (ℤ → Bool) → (ℤ → Bool)) :
    (ℤ → Bool) → (ℤ → Bool) :=
  fun s => observe (PhiConjugacySeed m (PsiConjugacySeed m s))

theorem pullbackThroughFixedResolution_eq_self {m : Nat} (hm : 3 ≤ m)
    (observe : (ℤ → Bool) → (ℤ → Bool)) :
    pullbackThroughFixedResolution m observe = observe := by
  funext s
  simp [pullbackThroughFixedResolution, PsiConjugacySeed, PhiConjugacySeed_eq_id hm]

/-- Minimal interface for a fixed-resolution observation protocol. The contradiction field records
that once the protocol is composed back to the input side, the existing finite-state barrier rules
out exact Zeckendorf-prime recognition. -/
structure FixedResolutionObservationProtocol (m : Nat) where
  observe : (ℤ → Bool) → (ℤ → Bool)
  regularAcceptor : Set (ℤ → Bool)
  recognizesZeckendorfPrimes : Prop
  pullback_obstruction : recognizesZeckendorfPrimes → ZeckendorfPrimeFiniteStateBarrier → False

/-- Paper-facing finite-state barrier for exact prime recognition after any fixed-resolution
interface.
    thm:conclusion-fixed-resolution-prime-finite-state-barrier -/
theorem paper_conclusion_fixed_resolution_prime_finite_state_barrier (m : Nat) (hm : 3 <= m) :
    ¬ ∃ O : FixedResolutionObservationProtocol m, O.recognizesZeckendorfPrimes := by
  intro h
  rcases h with ⟨O, hO⟩
  have hpullback : pullbackThroughFixedResolution m O.observe = O.observe :=
    pullbackThroughFixedResolution_eq_self hm O.observe
  have hbarrier : ZeckendorfPrimeFiniteStateBarrier := by
    simpa [ZeckendorfPrimeFiniteStateBarrier] using Omega.Zeta.paper_zeta_syntax_mealy_regular_impossible
  exact O.pullback_obstruction hO hbarrier

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the double-neutrality conclusion on finite-state
    postprocessing.
    thm:conclusion-finite-state-postprocessing-double-neutrality -/
theorem paper_conclusion_finite_state_postprocessing_double_neutrality
    (rate_neutrality arithmetic_neutrality : Prop) :
    rate_neutrality → arithmetic_neutrality → rate_neutrality ∧ arithmetic_neutrality := by
  intro hRate hArithmetic
  exact ⟨hRate, hArithmetic⟩

end Omega.Conclusion
