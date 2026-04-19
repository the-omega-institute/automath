import Omega.GU.GroupJGPrimeRegisterPhaseBohrDense

namespace Omega.GU

/-- Scaling both logarithmic generators by `2` preserves the same irrational log-ratio witness,
so the scanned phase subgroup stays dense.
    cor:group-jg-prime-register-phase-scan-dense -/
theorem paper_group_jg_prime_register_phase_scan_dense (D : GroupJGPrimeRegisterPhaseData) :
    Dense (AddSubgroup.closure {2 * D.t * Real.log (2 : ℝ), 2 * D.t * Real.log (3 : ℝ)} : Set ℝ) := by
  let D' : GroupJGPrimeRegisterPhaseData :=
    ⟨2 * D.t, mul_ne_zero (by norm_num) D.ht⟩
  simpa [D', GroupJGPrimeRegisterPhaseData.phaseImageDense, mul_assoc, mul_left_comm, mul_comm] using
    paper_group_jg_prime_register_phase_bohr_dense D'

end Omega.GU
