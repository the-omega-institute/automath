import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9f-sideinfo-expected-length-lower-bound`. -/
theorem paper_xi_time_part9f_sideinfo_expected_length_lower_bound
    (logM expectedLength entropyMicro entropyMacro fiberLog klResidual : ℝ)
    (hlogM : 0 < logM)
    (hCode : (entropyMicro - entropyMacro) / logM ≤ expectedLength)
    (hChain : entropyMicro - entropyMacro = fiberLog - klResidual) :
    (entropyMicro - entropyMacro) / logM ≤ expectedLength ∧
      (fiberLog - klResidual) / logM ≤ expectedLength := by
  have _logM_pos : 0 < logM := hlogM
  constructor
  · exact hCode
  · rw [← hChain]
    exact hCode

end Omega.Zeta
