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

/-- Paper-facing residual quotient probe: the prime-power quotient count splits into the free
`p^(kr)` contribution times a bounded torsion correction, and the correction is uniformly bounded
by the torsion size. -/
theorem paper_cdim_residual_quotient_probe (r t p k : Nat) :
    0 < t →
    phaseSpectrumCount r t (p ^ k) = p ^ (k * r) * Nat.gcd t (p ^ k) ∧
      Nat.gcd t (p ^ k) ≤ t ∧
      phaseSpectrumCount r t (p ^ k) ≤ p ^ (k * r) * t := by
  intro ht
  rcases paper_cdim_residual_quotient_probe_seeds r t p k ht with ⟨hcount, hgcd⟩
  refine ⟨hcount, hgcd, ?_⟩
  rw [hcount]
  exact Nat.mul_le_mul_left (p ^ (k * r)) hgcd

end Omega.CircleDimension
