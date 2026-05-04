import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_pick_poisson_energy_fixed_flux_extremal_prod_le_average_pow
    {κ : ℕ} (hκ : 0 < κ) (p : Fin κ → ℝ) (hp : ∀ j, 0 ≤ p j) :
    ∏ j, p j ≤ ((∑ j, p j) / (κ : ℝ)) ^ κ := by
  classical
  let P : ℝ := ∏ j, p j
  have hP_nonneg : 0 ≤ P := by
    exact Finset.prod_nonneg fun j _ => hp j
  have hsumw_pos : 0 < ∑ _j : Fin κ, (1 : ℝ) := by
    simp [hκ]
  have hamgm :=
    Real.geom_mean_le_arith_mean
      (s := (Finset.univ : Finset (Fin κ)))
      (w := fun _ => (1 : ℝ))
      (z := p)
      (by intro _ _; norm_num)
      hsumw_pos
      (by intro j _; exact hp j)
  have hamgm' : P ^ ((κ : ℝ)⁻¹) ≤ (∑ j, p j) / (κ : ℝ) := by
    simpa [P] using hamgm
  have hleft : (P ^ ((κ : ℝ)⁻¹)) ^ κ = P := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP_nonneg]
    have hκne : (κ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hκ)
    rw [inv_mul_cancel₀ hκne, Real.rpow_one]
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hP_nonneg _) hamgm' κ
  simpa [P, hleft] using hpow

/-- Paper label: `cor:xi-pick-poisson-energy-fixed-flux-extremal`. -/
theorem paper_xi_pick_poisson_energy_fixed_flux_extremal {κ : ℕ} (hκ : 0 < κ)
    (p : Fin κ → ℝ) (hp : ∀ j, 0 ≤ p j) (detP : ℝ)
    (hdet : detP ≤ ∏ j, p j) :
    detP ≤ ((∑ j, p j) / (κ : ℝ)) ^ κ := by
  exact le_trans hdet (xi_pick_poisson_energy_fixed_flux_extremal_prod_le_average_pow hκ p hp)

end Omega.Zeta
