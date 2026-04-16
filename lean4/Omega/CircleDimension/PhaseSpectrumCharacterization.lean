import Omega.CircleDimension.CircleDim
import Omega.CircleDimension.PhaseSpectrumMonoid

namespace Omega.CircleDimension

/-- Paper-facing characterization package for the phase spectrum:
    the closed form `N^r * gcd(t, N)`, the prime-factor monoid factorization,
    and exact reconstruction of the positive-torsion parameters from the full
    phase spectrum.
    thm:cdim-phase-spectrum-characterization -/
theorem paper_cdim_phase_spectrum_characterization :
    (∀ r t N : Nat, phaseSpectrumCount r t N = N ^ r * Nat.gcd t N) ∧
    (∀ r t : Nat, 0 < t → ∀ N : Nat,
      phaseSpectrumCount r t N =
        phaseSpectrumCount r 1 N *
          (t.factorization.support.prod fun p => phaseSpectrumCount 0 (p ^ t.factorization p) N)) ∧
    (∀ r r' t t' : Nat, 0 < t → 0 < t' →
      (∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) →
      r = r' ∧ t = t') := by
  refine ⟨phaseSpectrumCount_split, ?_, ?_⟩
  · intro r t ht N
    exact paper_cdim_phase_spectrum_monoid ht N
  · intro r r' t t' ht ht' h
    exact phaseSpectrumCount_reconstruction ht ht' h

end Omega.CircleDimension
