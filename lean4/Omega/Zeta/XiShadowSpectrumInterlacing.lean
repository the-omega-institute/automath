import Omega.Zeta.XiShadowSpectrumTowerPrincipalMinors

namespace Omega.Zeta

/-- Paper label: `con:xi-shadow-spectrum-interlacing`.

The already packaged shadow-spectrum tower theorem records, for every adjacent pair of tail
principal minors, the determinant-ratio Stieltjes layer together with the strict interlacing of
their spectra. -/
theorem paper_xi_shadow_spectrum_interlacing
    (D : xi_shadow_spectrum_tower_principal_minors_data) : D.statement := by
  exact paper_xi_shadow_spectrum_tower_principal_minors D

end Omega.Zeta
