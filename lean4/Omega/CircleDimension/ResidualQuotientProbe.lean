import Omega.CircleDimension.PhaseSpectrumQuotient
import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: prime-power finite quotients grow like `p^(kr)` up to a bounded torsion
    correction.
    prop:cdim-residual-quotient-probe -/
theorem paper_cdim_residual_quotient_probe_seeds (r t p k : Nat) :
    0 < t →
    phaseSpectrumCount r t (p ^ k) = p ^ (k * r) * Nat.gcd t (p ^ k) ∧
      Nat.gcd t (p ^ k) ≤ t := by
  intro ht
  constructor
  · simpa [pow_mul] using paper_cdim_phase_spectrum_quotient_seeds r t (p ^ k)
  · exact Nat.le_of_dvd ht (Nat.gcd_dvd_left t (p ^ k))

end Omega.CircleDimension
