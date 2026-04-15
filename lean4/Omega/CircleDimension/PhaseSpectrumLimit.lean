import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: the phase-spectrum limit theorem is controlled by the coprime/divisible
    dichotomy for `phaseSpectrumCount`, together with the free case `t = 0`.
    thm:cdim-phase-spectrum-limit -/
theorem paper_cdim_phase_spectrum_limit_seeds :
    (∀ r t N : Nat, Nat.Coprime t N → phaseSpectrumCount r t N = N ^ r) ∧
      (∀ r N : Nat, phaseSpectrumCount r 0 N = N ^ (r + 1)) ∧
      (∀ r t p : Nat, Nat.Prime p → p ∣ t → phaseSpectrumCount r t p = p ^ (r + 1)) ∧
      (∀ r t p : Nat, Nat.Prime p → ¬ p ∣ t → phaseSpectrumCount r t p = p ^ r) := by
  refine ⟨phaseSpectrumCount_coprime, phaseSpectrumCount_free, ?_, ?_⟩
  · intro r t p hp hpt
    simpa [Nat.add_comm] using phaseSpectrumCount_prime_dvd r t hp hpt
  · intro r t p hp hpt
    exact phaseSpectrumCount_prime_ndvd r t hp hpt

end Omega.CircleDimension
