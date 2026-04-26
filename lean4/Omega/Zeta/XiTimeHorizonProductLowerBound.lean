import Mathlib.Tactic

namespace Omega.Zeta

/-- The Cayley-image defect depth `h(ρ) = 1 - |w_ρ|²` in the explicit `(γ, δ)` coordinates used in
the paper. -/
noncomputable def xi_time_horizon_product_lower_bound_depth (γ δ : ℝ) : ℝ :=
  (4 * δ) / (γ ^ 2 + (δ + 1) ^ 2)

/-- The depth transform after `m` foldings. -/
noncomputable def xi_time_horizon_product_lower_bound_folded_depth (h : ℝ) (m : ℕ) : ℝ :=
  1 - (1 - h) ^ m

/-- The explicit reciprocal-depth quantity `Q_ρ`. -/
noncomputable def xi_time_horizon_product_lower_bound_Q (γ δ : ℝ) : ℝ :=
  (γ ^ 2 + (δ + 1) ^ 2) / (4 * δ)

/-- Concrete budget data for the mixed folding/horizon lower bound. The assumptions record the
positive Cayley-image depth parameter `δ`, the fold count `m`, and the previously established
horizon trigger at the folded depth. -/
structure xi_time_horizon_product_lower_bound_data where
  γ : ℝ
  δ : ℝ
  m : ℕ
  N : ℝ
  hδ : 0 < δ
  horizon_lb :
    1 / xi_time_horizon_product_lower_bound_folded_depth
        (xi_time_horizon_product_lower_bound_depth γ δ) m ≤ N
  folded_depth_pos :
    0 < xi_time_horizon_product_lower_bound_folded_depth
        (xi_time_horizon_product_lower_bound_depth γ δ) m

private lemma xi_time_horizon_product_lower_bound_depth_pos {γ δ : ℝ} (hδ : 0 < δ) :
    0 < xi_time_horizon_product_lower_bound_depth γ δ := by
  unfold xi_time_horizon_product_lower_bound_depth
  positivity

private lemma xi_time_horizon_product_lower_bound_depth_le_one {γ δ : ℝ} (hδ : 0 < δ) :
    xi_time_horizon_product_lower_bound_depth γ δ ≤ 1 := by
  unfold xi_time_horizon_product_lower_bound_depth
  have hden_pos : 0 < γ ^ 2 + (δ + 1) ^ 2 := by positivity
  have hnum_le_den : 4 * δ ≤ γ ^ 2 + (δ + 1) ^ 2 := by
    have hsq : 0 ≤ γ ^ 2 + (δ - 1) ^ 2 := by positivity
    nlinarith
  have hdiv :
      (4 * δ) / (γ ^ 2 + (δ + 1) ^ 2) ≤
        (γ ^ 2 + (δ + 1) ^ 2) / (γ ^ 2 + (δ + 1) ^ 2) := by
    exact div_le_div_of_nonneg_right hnum_le_den hden_pos.le
  simpa [hden_pos.ne'] using hdiv

private lemma xi_time_horizon_product_lower_bound_folded_depth_le {h : ℝ}
    (hh_nonneg : 0 ≤ h) (hh_le_one : h ≤ 1) :
    ∀ m : ℕ, xi_time_horizon_product_lower_bound_folded_depth h m ≤ (m : ℝ) * h
  | 0 => by
      simp [xi_time_horizon_product_lower_bound_folded_depth]
  | m + 1 => by
      have ih : xi_time_horizon_product_lower_bound_folded_depth h m ≤ (m : ℝ) * h :=
        xi_time_horizon_product_lower_bound_folded_depth_le hh_nonneg hh_le_one m
      calc
        xi_time_horizon_product_lower_bound_folded_depth h (m + 1)
            = h + (1 - h) *
                xi_time_horizon_product_lower_bound_folded_depth h m := by
              simp [xi_time_horizon_product_lower_bound_folded_depth, pow_succ]
              ring
        _ ≤ h + (1 - h) * ((m : ℝ) * h) := by
              have hone_nonneg : 0 ≤ 1 - h := by linarith
              gcongr
        _ ≤ h + (m : ℝ) * h := by
              have hmh_nonneg : 0 ≤ (m : ℝ) * h := by positivity
              nlinarith [hh_le_one, hmh_nonneg]
        _ = ((m + 1 : ℕ) : ℝ) * h := by
              norm_num
              ring

/-- Paper label: `thm:xi-time-horizon-product-lower-bound`. The folded depth satisfies
`h_m(a) = 1 - (1 - h(a))^m`, and the horizon trigger at inverse folded depth forces the mixed
budget inequality `Q_ρ ≤ m N`, where `Q_ρ = h(ρ)⁻¹` for the explicit Cayley-image defect depth. -/
theorem paper_xi_time_horizon_product_lower_bound
    (D : xi_time_horizon_product_lower_bound_data) :
    let h := xi_time_horizon_product_lower_bound_depth D.γ D.δ
    let hm := xi_time_horizon_product_lower_bound_folded_depth h D.m
    let Qρ := xi_time_horizon_product_lower_bound_Q D.γ D.δ
    hm = 1 - (1 - h) ^ D.m ∧ Qρ = 1 / h ∧ Qρ ≤ (D.m : ℝ) * D.N := by
  dsimp [xi_time_horizon_product_lower_bound_folded_depth, xi_time_horizon_product_lower_bound_Q]
  let h := xi_time_horizon_product_lower_bound_depth D.γ D.δ
  have hh_pos : 0 < h := xi_time_horizon_product_lower_bound_depth_pos D.hδ
  have hh_nonneg : 0 ≤ h := hh_pos.le
  have hh_le_one : h ≤ 1 := xi_time_horizon_product_lower_bound_depth_le_one D.hδ
  have hhm_le :
      xi_time_horizon_product_lower_bound_folded_depth h D.m ≤ (D.m : ℝ) * h := by
    exact xi_time_horizon_product_lower_bound_folded_depth_le hh_nonneg hh_le_one D.m
  have hmh_pos : 0 < (D.m : ℝ) * h := by
    exact lt_of_lt_of_le D.folded_depth_pos hhm_le
  have hm_real_pos : 0 < (D.m : ℝ) := by
    nlinarith
  have h_inv_mul_le : 1 / ((D.m : ℝ) * h) ≤ D.N := by
    have h_inv_le :
        1 / ((D.m : ℝ) * h) ≤
          1 / xi_time_horizon_product_lower_bound_folded_depth h D.m := by
      exact one_div_le_one_div_of_le D.folded_depth_pos hhm_le
    exact h_inv_le.trans D.horizon_lb
  have h_budget : 1 / h ≤ (D.m : ℝ) * D.N := by
    have hmul := mul_le_mul_of_nonneg_left h_inv_mul_le hm_real_pos.le
    calc
      1 / h = (D.m : ℝ) * (1 / ((D.m : ℝ) * h)) := by
        field_simp [hm_real_pos.ne', hh_pos.ne']
      _ ≤ (D.m : ℝ) * D.N := hmul
  have hQ :
      (D.γ ^ 2 + (D.δ + 1) ^ 2) / (4 * D.δ) = 1 / h := by
    dsimp [h, xi_time_horizon_product_lower_bound_depth]
    field_simp [D.hδ.ne']
  exact ⟨rfl, hQ, by simpa [hQ] using h_budget⟩

end Omega.Zeta
