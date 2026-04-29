import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete mod-`p` recovery data for a resonance-window Hankel block.

The rank-drop set and primitive torsion order define the excluded primes.  Away from them, the
rigidity fields identify the mod-`p` Hankel kernel with the multiplier module and normalize the
gcd recovered from a kernel basis to the reduced recurrence polynomial. -/
structure conclusion_resonance_window_goodprime_exact_modp_recovery_data where
  conclusion_resonance_window_goodprime_exact_modp_recovery_q : ℕ
  conclusion_resonance_window_goodprime_exact_modp_recovery_q_window :
    conclusion_resonance_window_goodprime_exact_modp_recovery_q ∈ Finset.Icc 9 17
  conclusion_resonance_window_goodprime_exact_modp_recovery_N : ℕ
  conclusion_resonance_window_goodprime_exact_modp_recovery_L : ℕ
  conclusion_resonance_window_goodprime_exact_modp_recovery_p : ℕ
  conclusion_resonance_window_goodprime_exact_modp_recovery_prime :
    Nat.Prime conclusion_resonance_window_goodprime_exact_modp_recovery_p
  conclusion_resonance_window_goodprime_exact_modp_recovery_minimalPolynomial :
    Polynomial (ZMod conclusion_resonance_window_goodprime_exact_modp_recovery_p)
  conclusion_resonance_window_goodprime_exact_modp_recovery_hankelKernel :
    Set (Polynomial (ZMod conclusion_resonance_window_goodprime_exact_modp_recovery_p))
  conclusion_resonance_window_goodprime_exact_modp_recovery_multiplierModule :
    Set (Polynomial (ZMod conclusion_resonance_window_goodprime_exact_modp_recovery_p))
  conclusion_resonance_window_goodprime_exact_modp_recovery_kernelBasis :
    Finset (Polynomial (ZMod conclusion_resonance_window_goodprime_exact_modp_recovery_p))
  conclusion_resonance_window_goodprime_exact_modp_recovery_recoveredGcd :
    Polynomial (ZMod conclusion_resonance_window_goodprime_exact_modp_recovery_p)
  conclusion_resonance_window_goodprime_exact_modp_recovery_badRankPrimes : Finset ℕ
  conclusion_resonance_window_goodprime_exact_modp_recovery_primitiveTorsionOrder : ℕ
  conclusion_resonance_window_goodprime_exact_modp_recovery_goodRankPrime :
    conclusion_resonance_window_goodprime_exact_modp_recovery_p ∉
      conclusion_resonance_window_goodprime_exact_modp_recovery_badRankPrimes
  conclusion_resonance_window_goodprime_exact_modp_recovery_goodTorsionPrime :
    ¬ conclusion_resonance_window_goodprime_exact_modp_recovery_p ∣
      conclusion_resonance_window_goodprime_exact_modp_recovery_primitiveTorsionOrder
  conclusion_resonance_window_goodprime_exact_modp_recovery_kernelRigidity :
    conclusion_resonance_window_goodprime_exact_modp_recovery_hankelKernel =
      conclusion_resonance_window_goodprime_exact_modp_recovery_multiplierModule
  conclusion_resonance_window_goodprime_exact_modp_recovery_gcdRecovery :
    conclusion_resonance_window_goodprime_exact_modp_recovery_recoveredGcd =
      conclusion_resonance_window_goodprime_exact_modp_recovery_minimalPolynomial

namespace conclusion_resonance_window_goodprime_exact_modp_recovery_data

/-- The good-prime predicate used by the resonance-window recovery statement. -/
def conclusion_resonance_window_goodprime_exact_modp_recovery_goodPrime
    (D : conclusion_resonance_window_goodprime_exact_modp_recovery_data) : Prop :=
  D.conclusion_resonance_window_goodprime_exact_modp_recovery_p ∉
      D.conclusion_resonance_window_goodprime_exact_modp_recovery_badRankPrimes ∧
    ¬ D.conclusion_resonance_window_goodprime_exact_modp_recovery_p ∣
      D.conclusion_resonance_window_goodprime_exact_modp_recovery_primitiveTorsionOrder

/-- Concrete statement for
`thm:conclusion-resonance-window-goodprime-exact-modp-recovery`. -/
def conclusion_resonance_window_goodprime_exact_modp_recovery_statement
    (D : conclusion_resonance_window_goodprime_exact_modp_recovery_data) : Prop :=
  D.conclusion_resonance_window_goodprime_exact_modp_recovery_q ∈ Finset.Icc 9 17 ∧
    Nat.Prime D.conclusion_resonance_window_goodprime_exact_modp_recovery_p ∧
    D.conclusion_resonance_window_goodprime_exact_modp_recovery_goodPrime ∧
    D.conclusion_resonance_window_goodprime_exact_modp_recovery_hankelKernel =
      D.conclusion_resonance_window_goodprime_exact_modp_recovery_multiplierModule ∧
    D.conclusion_resonance_window_goodprime_exact_modp_recovery_recoveredGcd =
      D.conclusion_resonance_window_goodprime_exact_modp_recovery_minimalPolynomial

end conclusion_resonance_window_goodprime_exact_modp_recovery_data

/-- Paper label: `thm:conclusion-resonance-window-goodprime-exact-modp-recovery`. -/
theorem paper_conclusion_resonance_window_goodprime_exact_modp_recovery
    (D : conclusion_resonance_window_goodprime_exact_modp_recovery_data) :
    D.conclusion_resonance_window_goodprime_exact_modp_recovery_statement := by
  exact
    ⟨D.conclusion_resonance_window_goodprime_exact_modp_recovery_q_window,
      D.conclusion_resonance_window_goodprime_exact_modp_recovery_prime,
      ⟨D.conclusion_resonance_window_goodprime_exact_modp_recovery_goodRankPrime,
        D.conclusion_resonance_window_goodprime_exact_modp_recovery_goodTorsionPrime⟩,
      D.conclusion_resonance_window_goodprime_exact_modp_recovery_kernelRigidity,
      D.conclusion_resonance_window_goodprime_exact_modp_recovery_gcdRecovery⟩

end Omega.Conclusion
