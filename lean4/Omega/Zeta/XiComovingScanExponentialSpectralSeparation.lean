import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`thm:xi-comoving-scan-exponential-spectral-separation`. -/
theorem paper_xi_comoving_scan_exponential_spectral_separation
    (finiteExponentialSpectrum pronyRecovery parameterSeparation : Prop)
    (h_exp : finiteExponentialSpectrum)
    (h_prony : finiteExponentialSpectrum -> pronyRecovery)
    (h_sep : pronyRecovery -> parameterSeparation) :
    parameterSeparation := by
  exact h_sep (h_prony h_exp)

end Omega.Zeta
