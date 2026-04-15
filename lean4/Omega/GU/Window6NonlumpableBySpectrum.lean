import Omega.GU.StrongLumpabilitySpectralFalsifier
import Omega.GU.StrongLumpabilitySpectralRigidity

namespace Omega.GU.Window6NonlumpableBySpectrum

/-- Paper-facing spectral obstruction to any equitable/lumpable window-`6` quotient.
    cor:terminal-window6-nonlumpable-by-spectrum -/
theorem paper_terminal_window6_nonlumpable_by_spectrum :
    (4841 : ℚ) / 10000 ∉ Omega.GU.hypercubeSpectrumSix ∧
      (6031 : ℚ) / 10000 ∉ Omega.GU.hypercubeSpectrumSix := by
  exact Omega.GU.paper_window6_strong_lumpability_spectral_falsifier

end Omega.GU.Window6NonlumpableBySpectrum
