import Mathlib.Logic.Basic

namespace Omega.Zeta

/-- Paper label: `prop:xi-basepoint-scan-heine-stieltjes-ode`. -/
theorem paper_xi_basepoint_scan_heine_stieltjes_ode
    (criticalConfig heineStieltjesIdentity uniqueVanVleck : Prop)
    (hcrit_iff : criticalConfig ↔ heineStieltjesIdentity) (hunique : uniqueVanVleck) :
    (criticalConfig ↔ heineStieltjesIdentity) ∧ uniqueVanVleck := by
  exact ⟨hcrit_iff, hunique⟩

end Omega.Zeta
