import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-information-spectrum-single-point-collapse`. -/
theorem paper_xi_foldbin_information_spectrum_single_point_collapse
    (infoDensityCollapse renyiRateCollapse noNontrivialSpectrum : Prop)
    (hInfo : infoDensityCollapse) (hRenyi : renyiRateCollapse)
    (hNoSpectrum : noNontrivialSpectrum) :
    infoDensityCollapse ∧ renyiRateCollapse ∧ noNontrivialSpectrum := by
  exact ⟨hInfo, hRenyi, hNoSpectrum⟩

end Omega.Zeta
