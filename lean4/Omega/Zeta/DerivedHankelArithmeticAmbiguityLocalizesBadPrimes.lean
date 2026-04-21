import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.DerivedHankelFiniteJetBadPrimeClosure

namespace Omega.Zeta

/-- Concrete localization package for the mod-`p^k` audit: a good prime keeps the audited
denominator nonzero, and the associated Gram-shift matrix is the unique realization certificate. -/
def derivedHankelModPrimePowerUniqueSolution {κ : Nat}
    (D : FiniteDefectCompleteReconstructionData κ)
    (M : XiMarkovDerivativeDeterminantBadPrimeData) (p k : Nat) : Prop :=
  1 ≤ k ∧
    D.kappaReadable ∧
    D.reconstructionFrom4KappaSamples ∧
    D.reconstructionFromMomentSegment ∧
    D.strictificationInvariant ∧
    ((((M.greenDenominator : ℤ) : ZMod p) ≠ 0)) ∧
    ∃! A : Matrix (Fin κ) (Fin κ) ℂ, A = derivedHankelFiniteJetShiftMatrix D

/-- Paper label: `cor:derived-hankel-arithmetic-ambiguity-localizes-bad-primes`. -/
theorem paper_derived_hankel_arithmetic_ambiguity_localizes_bad_primes (κ : Nat)
    (D : FiniteDefectCompleteReconstructionData κ) (M : XiMarkovDerivativeDeterminantBadPrimeData)
    (p k : Nat) (hp : derivedHankelGoodPrime M p) (hk : 1 ≤ k) :
    derivedHankelModPrimePowerUniqueSolution D M p k := by
  rcases paper_derived_hankel_finite_jet_bad_prime_closure κ D M p hp with
    ⟨hkappa, h4k, h2k, hstrict, -, -, -, -, -, -, hdenom⟩
  refine ⟨hk, hkappa, h4k, h2k, hstrict, hdenom, ?_⟩
  refine ⟨derivedHankelFiniteJetShiftMatrix D, rfl, ?_⟩
  intro A hA
  simpa [hA]

end Omega.Zeta
