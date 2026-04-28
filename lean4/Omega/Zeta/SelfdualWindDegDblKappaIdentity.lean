import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:selfdual-wind-deg-dbl-kappa-identity`. -/
theorem paper_selfdual_wind_deg_dbl_kappa_identity
    (wind degBl dBl kappa : ℕ) (hwind : wind = degBl) (hmodel : degBl = dBl)
    (hpoles : dBl = kappa) :
    wind = degBl ∧ degBl = dBl ∧ dBl = kappa ∧ wind = kappa := by
  exact ⟨hwind, hmodel, hpoles, hwind.trans (hmodel.trans hpoles)⟩

end Omega.Zeta
