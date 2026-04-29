import Mathlib.Tactic

namespace Omega.Zeta

lemma xi_cayley_offset_defect_spectrum_bounds_pointwise (gamma delta : ℝ)
    (hdelta : 0 < delta)
    (hden : 0 < gamma ^ 2 + (delta - 1) ^ 2) :
    (2 * delta) / (gamma ^ 2 + (delta + 1) ^ 2) ≤
      (1 / 2 : ℝ) *
        Real.log ((gamma ^ 2 + (delta + 1) ^ 2) /
          (gamma ^ 2 + (delta - 1) ^ 2)) ∧
    (1 / 2 : ℝ) *
        Real.log ((gamma ^ 2 + (delta + 1) ^ 2) /
          (gamma ^ 2 + (delta - 1) ^ 2)) ≤
      (2 * delta) / (gamma ^ 2 + (delta - 1) ^ 2) := by
  set a : ℝ := gamma ^ 2 + (delta - 1) ^ 2 with ha
  have ha_pos : 0 < a := by simpa [a] using hden
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hnum : gamma ^ 2 + (delta + 1) ^ 2 = a + 4 * delta := by
    rw [ha]
    ring
  have hb_pos : 0 < a + 4 * delta := by nlinarith
  have hb_ne : a + 4 * delta ≠ 0 := ne_of_gt hb_pos
  have hx_pos : 0 < 1 + (4 * delta) / a := by positivity
  have hratio :
      (gamma ^ 2 + (delta + 1) ^ 2) / (gamma ^ 2 + (delta - 1) ^ 2) =
        1 + (4 * delta) / a := by
    rw [hnum, ← ha]
    field_simp [ha_ne]
  have hlog_upper : Real.log (1 + (4 * delta) / a) ≤ (4 * delta) / a := by
    have h := Real.log_le_sub_one_of_pos hx_pos
    linarith
  have hupper :
      (1 / 2 : ℝ) * Real.log
          ((gamma ^ 2 + (delta + 1) ^ 2) / (gamma ^ 2 + (delta - 1) ^ 2)) ≤
        (2 * delta) / a := by
    rw [hratio]
    have hmul :=
      mul_le_mul_of_nonneg_left hlog_upper (by norm_num : 0 ≤ (1 / 2 : ℝ))
    have hhalf : (1 / 2 : ℝ) * ((4 * delta) / a) = (2 * delta) / a := by
      ring
    nlinarith
  have hlog_lower : 1 - (1 + (4 * delta) / a)⁻¹ ≤
      Real.log (1 + (4 * delta) / a) :=
    Real.one_sub_inv_le_log_of_pos hx_pos
  have hlower_eq :
      (1 / 2 : ℝ) * (1 - (1 + (4 * delta) / a)⁻¹) =
        (2 * delta) / (a + 4 * delta) := by
    field_simp [ha_ne, hb_ne]
    ring
  have hlower :
      (2 * delta) / (a + 4 * delta) ≤
        (1 / 2 : ℝ) * Real.log
          ((gamma ^ 2 + (delta + 1) ^ 2) / (gamma ^ 2 + (delta - 1) ^ 2)) := by
    rw [hratio]
    rw [← hlower_eq]
    exact mul_le_mul_of_nonneg_left hlog_lower (by norm_num : 0 ≤ (1 / 2 : ℝ))
  constructor
  · simpa [hnum] using hlower
  · simpa [a] using hupper

/-- Paper label: `thm:xi-cayley-offset-defect-spectrum-bounds`. -/
theorem paper_xi_cayley_offset_defect_spectrum_bounds (k : ℕ) (gamma delta : Fin k → ℝ)
    (hdelta : ∀ j, 0 < delta j)
    (hden : ∀ j, 0 < gamma j ^ 2 + (delta j - 1) ^ 2) (defectLog : ℝ)
    (hdef :
      defectLog =
        ∑ j : Fin k,
          (1 / 2 : ℝ) *
            Real.log
              ((gamma j ^ 2 + (delta j + 1) ^ 2) /
                (gamma j ^ 2 + (delta j - 1) ^ 2))) :
    (∑ j : Fin k, (2 * delta j) / (gamma j ^ 2 + (delta j + 1) ^ 2)) ≤
        defectLog ∧
      defectLog ≤
        (∑ j : Fin k, (2 * delta j) / (gamma j ^ 2 + (delta j - 1) ^ 2)) := by
  rw [hdef]
  constructor
  · exact Finset.sum_le_sum fun j _ =>
      (xi_cayley_offset_defect_spectrum_bounds_pointwise (gamma j) (delta j)
        (hdelta j) (hden j)).1
  · exact Finset.sum_le_sum fun j _ =>
      (xi_cayley_offset_defect_spectrum_bounds_pointwise (gamma j) (delta j)
        (hdelta j) (hden j)).2

end Omega.Zeta
