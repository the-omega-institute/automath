import Mathlib.Tactic
import Omega.Zeta.DerivedHankelArithmeticAmbiguityLocalizesBadPrimes
import Omega.Zeta.XiEntropyGapExponentialSuppressionNonzeroFingerprint

namespace Omega.Zeta

theorem paper_derived_hankel_sampling_badprime_entropy_unified
    (κ : Nat) (D : FiniteDefectCompleteReconstructionData κ)
    (M : XiMarkovDerivativeDeterminantBadPrimeData) (p k : Nat)
    (hp : derivedHankelGoodPrime M p) (hk : 1 ≤ k)
    (mass delta phase : Fin κ → ℝ) (hm : ∀ j, 0 ≤ mass j) (hδ : ∀ j, 0 < delta j)
    (hphase : ∀ j, |phase j| ≤ 1) :
    derivedHankelModPrimePowerUniqueSolution D M p k ∧
      D.kappaReadable ∧
      |xiComovingFourier mass delta phase 1| ≤
        4 * Real.pi * Real.exp (-(1 : ℝ)) * xiEntropyGap mass delta := by
  have hunique :=
    paper_derived_hankel_arithmetic_ambiguity_localizes_bad_primes κ D M p k hp hk
  have hreadable := (paper_xi_finite_defect_complete_reconstruction κ D).1
  have hbound :=
    (paper_xi_entropy_gap_exponential_suppression_nonzero_fingerprint
      mass delta phase hm hδ hphase (n := 1) (by norm_num)).1
  exact ⟨hunique, hreadable, by simpa using hbound⟩

end Omega.Zeta
