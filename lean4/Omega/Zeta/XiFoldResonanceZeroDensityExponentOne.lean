import Mathlib

namespace Omega.Zeta

/-- Paper label: `cor:xi-fold-resonance-zero-density-exponent-one`. -/
theorem paper_xi_fold_resonance_zero_density_exponent_one
    (Nphi : ℝ → ℕ)
    (hlinear : ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ R, R0 ≤ R → |(Nphi R : ℝ) - 2 * R| ≤ C * Real.log R) :
    Filter.Tendsto (fun R : ℝ => (Nphi R : ℝ) / (2 * R)) Filter.atTop (nhds 1) := by
  obtain ⟨C, R0, hC, hR0, hbound⟩ := hlinear
  have hlogdiv : Filter.Tendsto (fun R : ℝ => Real.log R / R) Filter.atTop (nhds 0) := by
    simpa [id] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hmajor :
      Filter.Tendsto (fun R : ℝ => (C / 2) * (Real.log R / R)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hlogdiv : Filter.Tendsto
      (fun R : ℝ => (C / 2) * (Real.log R / R)) Filter.atTop (nhds ((C / 2) * 0)))
  have herror :
      Filter.Tendsto (fun R : ℝ => (Nphi R : ℝ) / (2 * R) - 1) Filter.atTop
        (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _) ?_ hmajor
    filter_upwards [Filter.eventually_ge_atTop R0] with R hR
    have hR1 : 1 ≤ R := le_trans hR0 hR
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hdenpos : 0 < 2 * R := by positivity
    have habs := hbound R hR
    have hrewrite :
        ‖(Nphi R : ℝ) / (2 * R) - 1‖ =
          |(Nphi R : ℝ) - 2 * R| / (2 * R) := by
      rw [Real.norm_eq_abs]
      have hden_ne : 2 * R ≠ 0 := ne_of_gt hdenpos
      calc
        |(Nphi R : ℝ) / (2 * R) - 1|
            = |((Nphi R : ℝ) - 2 * R) / (2 * R)| := by
                congr 1
                field_simp [hden_ne]
        _ = |(Nphi R : ℝ) - 2 * R| / (2 * R) := by
                rw [abs_div, abs_of_pos hdenpos]
    rw [hrewrite]
    have hdiv := div_le_div_of_nonneg_right habs (le_of_lt hdenpos)
    calc
      |(Nphi R : ℝ) - 2 * R| / (2 * R) ≤ C * Real.log R / (2 * R) := hdiv
      _ = (C / 2) * (Real.log R / R) := by ring
  have hsum :
      Filter.Tendsto (fun R : ℝ => 1 + ((Nphi R : ℝ) / (2 * R) - 1)) Filter.atTop
        (nhds (1 + 0)) :=
    tendsto_const_nhds.add herror
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum

end Omega.Zeta
