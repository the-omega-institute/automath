import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-horizon-pole-residue-depth-strength`. -/
theorem paper_xi_horizon_pole_residue_depth_strength (m : ℕ) (δ γ h resNorm : ℝ)
    (hδ : 0 < δ)
    (hh : h = 4 * δ / (γ ^ 2 + (1 + δ) ^ 2))
    (hres : resNorm = 2 * (m : ℝ) / (γ ^ 2 + (1 + δ) ^ 2)) :
    resNorm = ((m : ℝ) / (2 * δ)) * h := by
  have hden_pos : 0 < γ ^ 2 + (1 + δ) ^ 2 := by
    nlinarith [sq_nonneg γ, sq_pos_of_pos (by linarith : 0 < 1 + δ)]
  rw [hres, hh]
  field_simp [hδ.ne', hden_pos.ne']
  ring

end Omega.Zeta
