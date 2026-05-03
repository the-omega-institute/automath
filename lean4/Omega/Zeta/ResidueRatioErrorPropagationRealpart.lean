import Mathlib.Tactic

namespace Omega.Zeta

/-- Relative residue-ratio errors propagate through one quotient with denominator margin
`1 - ε`. -/
theorem paper_xi_residue_ratio_error_propagation_realpart {𝕜 : Type*} [NormedField 𝕜]
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) {δj δnext : 𝕜}
    (hj : ‖δj‖ ≤ ε) (hnext : ‖δnext‖ ≤ ε) :
    ‖((1 + δj) / (1 + δnext) - 1 : 𝕜)‖ ≤ (2 * ε) / (1 - ε) := by
  have hδnext_lt_one : ‖δnext‖ < 1 := lt_of_le_of_lt hnext hε1
  have hden_ne : (1 + δnext : 𝕜) ≠ 0 := by
    intro hzero
    have hδ : δnext = -1 := by
      have hsub := congrArg (fun x : 𝕜 => x - 1) hzero
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have hnorm : ‖δnext‖ = 1 := by
      rw [hδ, norm_neg, norm_one]
    linarith
  have hden_pos : 0 < ‖(1 + δnext : 𝕜)‖ := norm_pos_iff.mpr hden_ne
  have hmargin_pos : 0 < 1 - ε := by linarith
  have hnum_le : ‖δj - δnext‖ ≤ 2 * ε := by
    calc
      ‖δj - δnext‖ ≤ ‖δj‖ + ‖δnext‖ := norm_sub_le δj δnext
      _ ≤ ε + ε := add_le_add hj hnext
      _ = 2 * ε := by ring
  have hden_lower : 1 - ε ≤ ‖(1 + δnext : 𝕜)‖ := by
    have htri : ‖(1 : 𝕜)‖ ≤ ‖(1 + δnext : 𝕜)‖ + ‖δnext‖ := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (norm_sub_le (1 + δnext : 𝕜) δnext)
    rw [norm_one] at htri
    linarith
  have hrewrite :
      ((1 + δj) / (1 + δnext) - 1 : 𝕜) = (δj - δnext) / (1 + δnext) := by
    field_simp [hden_ne]
    ring
  calc
    ‖((1 + δj) / (1 + δnext) - 1 : 𝕜)‖ = ‖(δj - δnext) / (1 + δnext)‖ := by
      rw [hrewrite]
    _ = ‖δj - δnext‖ / ‖(1 + δnext : 𝕜)‖ := by
      rw [norm_div]
    _ ≤ (2 * ε) / ‖(1 + δnext : 𝕜)‖ := by
      exact div_le_div_of_nonneg_right hnum_le hden_pos.le
    _ ≤ (2 * ε) / (1 - ε) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hden_pos hmargin_pos).2 hden_lower)
        (by nlinarith)

end Omega.Zeta
