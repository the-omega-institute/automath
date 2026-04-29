import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-basepoint-scan-anchor-det-global-maximum`. -/
theorem paper_xi_basepoint_scan_anchor_det_global_maximum {κ : ℕ}
    (Omega : (Fin κ → ℝ) → Prop)
    (attainsGlobalMaximum criticalConfiguration heineStieltjesWitness : (Fin κ → ℝ) → Prop)
    (h_exists : ∃ X, Omega X ∧ attainsGlobalMaximum X)
    (hcrit : ∀ X, Omega X → attainsGlobalMaximum X → criticalConfiguration X)
    (hode : ∀ X, criticalConfiguration X → heineStieltjesWitness X) :
    ∃ X, Omega X ∧ attainsGlobalMaximum X ∧ criticalConfiguration X ∧
      heineStieltjesWitness X := by
  rcases h_exists with ⟨X, hOmega, hmax⟩
  have hcritical : criticalConfiguration X := hcrit X hOmega hmax
  have hwitness : heineStieltjesWitness X := hode X hcritical
  exact ⟨X, hOmega, hmax, hcritical, hwitness⟩

end Omega.Zeta
