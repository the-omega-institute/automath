import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: phase-sampling counts are exactly the finite quotient cardinalities
    `|G / NG|`, encoded here by the closed form `N^r * gcd(t, N)` for finitely generated
    abelian groups with free rank `r` and torsion parameter `t`.
    prop:cdim-phase-spectrum-quotient -/
theorem paper_cdim_phase_spectrum_quotient_seeds :
    ∀ r t N : Nat, phaseSpectrumCount r t N = N ^ r * Nat.gcd t N := by
  intro r t N
  exact phaseSpectrumCount_split r t N

/-- Paper-facing wrapper for the finite quotient closed form.
    prop:cdim-phase-spectrum-quotient -/
theorem paper_cdim_phase_spectrum_quotient :
    ∀ r t N : Nat, phaseSpectrumCount r t N = N ^ r * Nat.gcd t N := by
  exact paper_cdim_phase_spectrum_quotient_seeds

end Omega.CircleDimension
