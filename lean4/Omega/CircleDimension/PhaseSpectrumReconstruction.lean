import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Paper-facing seed for exact reconstruction from phase-sampling counts.
    thm:cdim-phase-spectrum-reconstruction -/
theorem paper_cdim_phase_spectrum_reconstruction_seeds
    {r r' t t' : Nat} (ht : 0 < t) (ht' : 0 < t') :
    (∀ N : Nat, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) ↔
      r = r' ∧ t = t' :=
  paper_phaseSpectrumCount_reconstruction_iff ht ht'

end Omega.CircleDimension
