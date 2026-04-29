import Mathlib.Tactic
import Omega.Zeta.XiComovingDefectLatticeCertificateBandExclusion

namespace Omega.Zeta

/-- Paper label: `cor:xi-comoving-finite-centers-band-exclusion`. Any finite-center cover by the
explicit visible half-window inherits the existing lattice-certificate band exclusion. -/
theorem paper_xi_comoving_finite_centers_band_exclusion
    (varrho eps delta0 T : ℝ) (centers : Finset ℝ)
    (hdelta0 : 0 < delta0 ∧ delta0 ≤ 1 / 2)
    (_hH : 0 < Omega.Zeta.xiComovingDefectVisibleWindow varrho eps delta0)
    (_hcover :
      ∀ γ ∈ Set.Icc (-(T - Omega.Zeta.xiComovingDefectVisibleWindow varrho eps delta0))
        (T - Omega.Zeta.xiComovingDefectVisibleWindow varrho eps delta0),
        ∃ x ∈ centers, |γ - x| < Omega.Zeta.xiComovingDefectVisibleWindow varrho eps delta0) :
    Omega.Zeta.noOffcriticalZeroInBand 1 delta0 := by
  simpa using
    (paper_xi_comoving_defect_lattice_certificate_band_exclusion varrho eps delta0).2.2.2.2.2
      hdelta0

end Omega.Zeta
