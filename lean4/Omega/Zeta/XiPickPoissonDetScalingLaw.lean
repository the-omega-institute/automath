import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper: `prop:xi-pick-poisson-det-scaling-law`. The pairwise pseudohyperbolic
factors are unchanged, while the `κ` Poisson factors each scale by `m⁻¹`. -/
theorem paper_xi_pick_poisson_det_scaling_law {κ : ℕ} (m : ℝ) (hm : 0 < m)
    (p pScaled : Fin κ → ℝ) (rho : Fin κ → Fin κ → ℝ) (detP detPScaled : ℝ)
    (hp : ∀ j, pScaled j = p j / m)
    (hdet :
      detP =
        (∏ j, p j) * ∏ j : Fin κ, ∏ k : Fin κ, if j < k then rho j k ^ 2 else 1)
    (hdetScaled :
      detPScaled =
        (∏ j, pScaled j) *
          ∏ j : Fin κ, ∏ k : Fin κ, if j < k then rho j k ^ 2 else 1) :
    detPScaled = detP / m ^ κ := by
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have hpow_ne : m ^ κ ≠ 0 := pow_ne_zero κ hm_ne
  have hprodScaled : (∏ j, pScaled j) = (∏ j, p j) / m ^ κ := by
    calc
      (∏ j, pScaled j) = ∏ j : Fin κ, p j / m := by
        exact Finset.prod_congr rfl (fun j _ => hp j)
      _ = (∏ j : Fin κ, p j) / ∏ _j : Fin κ, m := by
        rw [Finset.prod_div_distrib]
      _ = (∏ j : Fin κ, p j) / m ^ κ := by
        simp
  rw [hdetScaled, hprodScaled, hdet]
  field_simp [hpow_ne]

end Omega.Zeta
