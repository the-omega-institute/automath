import Omega.TypedAddressBiaxialCompletion.ComovingFirstOrder

theorem paper_xi_comoving_prefix_bit_budget_gain {δ δ0 γ : ℝ} (hδ0_pos : 0 < δ0)
    (hδ0_lt : δ0 < 1) (hδ : δ0 ≤ δ) (hδ_lt : δ < 1) :
    Omega.TypedAddressBiaxialCompletion.typedAddressComovingChartDepth δ γ γ =
        (4 * δ) / (1 + δ) ^ 2 ∧
      (4 * δ0) / (1 + δ0) ^ 2 ≤
        Omega.TypedAddressBiaxialCompletion.typedAddressComovingChartDepth δ γ γ := by
  have hδ_nonneg : 0 ≤ δ := le_trans hδ0_pos.le hδ
  have hchart :
      Omega.TypedAddressBiaxialCompletion.typedAddressComovingChartDepth δ γ γ =
        (4 * δ) / (1 + δ) ^ 2 :=
    (Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_first_order
      (δ := δ) (γ := γ) hδ_nonneg).2
  refine ⟨hchart, ?_⟩
  rw [hchart]
  have hden0_pos : 0 < (1 + δ0) ^ 2 := by nlinarith
  have hden_pos : 0 < (1 + δ) ^ 2 := by nlinarith
  have hδ_pos : 0 < δ := lt_of_lt_of_le hδ0_pos hδ
  have hprod_lt : δ0 * δ < 1 := by
    have hmul_lt : δ0 * δ < 1 * δ := mul_lt_mul_of_pos_right hδ0_lt hδ_pos
    nlinarith
  have hcore : δ0 * (1 + δ) ^ 2 ≤ δ * (1 + δ0) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hprod_lt.le)]
  rw [div_le_div_iff₀ hden0_pos hden_pos]
  nlinarith
