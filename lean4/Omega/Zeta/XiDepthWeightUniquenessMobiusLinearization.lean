import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-depth-weight-uniqueness-mobius-linearization`. Specializing the Möbius
functional equation at `m = 1 / δ` reduces the conclusion to a one-line algebraic solve. -/
theorem paper_xi_depth_weight_uniqueness_mobius_linearization (p : ℝ → ℝ)
    (hcod : forall δ, 0 < δ -> 0 < p δ ∧ p δ < 1)
    (hphi : forall m δ, 0 < m -> 0 < δ ->
      p (m * δ) = (m * p δ) / (1 + (m - 1) * p δ))
    (hhalf : p 1 = 1 / 2) :
    forall δ, 0 < δ -> p δ = δ / (1 + δ) := by
  intro δ hδ
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hpδ := hcod δ hδ
  have hpδ_pos : 0 < p δ := hpδ.1
  have hspecial :=
    hphi (1 / δ) δ (one_div_pos.mpr hδ) hδ
  have hspecial' : p 1 = ((1 / δ) * p δ) / (1 + ((1 / δ) - 1) * p δ) := by
    simpa [hδne] using hspecial
  rw [hhalf] at hspecial'
  have hnum_pos : 0 < (1 / δ) * p δ := by
    exact mul_pos (one_div_pos.mpr hδ) hpδ_pos
  have hden_pos : 0 < 1 + ((1 / δ) - 1) * p δ := by
    have hright_pos :
        0 < ((1 / δ) * p δ) / (1 + ((1 / δ) - 1) * p δ) := by
      rw [← hspecial']
      norm_num
    by_contra hnot
    have hle : 1 + ((1 / δ) - 1) * p δ ≤ 0 := not_lt.mp hnot
    have hright_nonpos :
        ((1 / δ) * p δ) / (1 + ((1 / δ) - 1) * p δ) ≤ 0 := by
      exact div_nonpos_of_nonneg_of_nonpos hnum_pos.le hle
    linarith
  have hrewrite : 1 + ((1 / δ) - 1) * p δ = (δ + p δ - δ * p δ) / δ := by
    field_simp [hδne]
    ring
  have hspecial'' : (1 / 2 : ℝ) = p δ / (δ + p δ - δ * p δ) := by
    calc
      (1 / 2 : ℝ) = ((1 / δ) * p δ) / (1 + ((1 / δ) - 1) * p δ) := hspecial'
      _ = ((1 / δ) * p δ) / ((δ + p δ - δ * p δ) / δ) := by rw [hrewrite]
      _ = p δ / (δ + p δ - δ * p δ) := by
        field_simp [hδne]
  have hden2_pos : 0 < δ + p δ - δ * p δ := by
    have hmul_pos : 0 < δ * (1 + ((1 / δ) - 1) * p δ) := mul_pos hδ hden_pos
    nlinarith [hrewrite]
  have hcross : δ + p δ - δ * p δ = 2 * p δ := by
    have hcross_half : (1 / 2 : ℝ) * (δ + p δ - δ * p δ) = p δ :=
      (eq_div_iff hden2_pos.ne').mp hspecial''
    nlinarith
  have hmul : p δ * (1 + δ) = δ := by
    nlinarith
  have hδ1_pos : 0 < 1 + δ := by linarith
  exact (eq_div_iff hδ1_pos.ne').2 <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

end Omega.Zeta
