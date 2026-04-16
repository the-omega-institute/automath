import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Paper-facing seed for exact reconstruction from phase-sampling counts.
    thm:cdim-phase-spectrum-reconstruction -/
theorem paper_cdim_phase_spectrum_reconstruction_seeds
    {r r' t t' : Nat} (ht : 0 < t) (ht' : 0 < t') :
    (∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) ↔
      r = r' ∧ t = t' :=
  paper_phaseSpectrumCount_reconstruction_iff ht ht'

/-- Unsuffixed paper-facing wrapper bundling uniqueness with the explicit recovery package.
    thm:cdim-phase-spectrum-reconstruction -/
theorem paper_cdim_phase_spectrum_reconstruction
    {r r' t t' : Nat} (ht : 0 < t) (ht' : 0 < t') :
    ((∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) ↔
      r = r' ∧ t = t') ∧
    ((∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) →
      (r = r' ∧ t = t') ∧ (r = r') ∧ (r = r' → t = t')) := by
  refine ⟨paper_cdim_phase_spectrum_reconstruction_seeds ht ht', ?_⟩
  intro h
  exact paper_phaseSpectrumCount_reconstruction_core ht ht' h

end Omega.CircleDimension
