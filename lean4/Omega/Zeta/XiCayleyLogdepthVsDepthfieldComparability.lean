import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.CayleyOffsetDefectSpectrumBounds

namespace Omega.Zeta

/-- Paper label: `cor:xi-cayley-logdepth-vs-depthfield-comparability`. -/
theorem paper_xi_cayley_logdepth_vs_depthfield_comparability (x δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    let h : ℝ := 4 * δ / (x ^ 2 + (1 + δ) ^ 2)
    let u : ℝ := -Real.log
      (Real.sqrt ((x ^ 2 + (1 - δ) ^ 2) / (x ^ 2 + (1 + δ) ^ 2)))
    (1 / 2 : ℝ) * h ≤ u ∧ u ≤ ((1 + δ) ^ 2 / (2 * (1 - δ) ^ 2)) * h := by
  dsimp
  have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hδ_ne_one : δ - 1 ≠ 0 := by linarith
  have hone_sub_ne : 1 - δ ≠ 0 := by linarith
  have hone_add_pos : 0 < 1 + δ := by linarith
  have hden_minus_delta : 0 < x ^ 2 + (δ - 1) ^ 2 :=
    add_pos_of_nonneg_of_pos hx2_nonneg (sq_pos_of_ne_zero hδ_ne_one)
  have hden_minus_one : 0 < x ^ 2 + (1 - δ) ^ 2 :=
    add_pos_of_nonneg_of_pos hx2_nonneg (sq_pos_of_ne_zero hone_sub_ne)
  have hden_plus_one : 0 < x ^ 2 + (1 + δ) ^ 2 :=
    add_pos_of_nonneg_of_pos hx2_nonneg (sq_pos_of_ne_zero (ne_of_gt hone_add_pos))
  have hden_plus_delta : 0 < x ^ 2 + (δ + 1) ^ 2 := by
    simpa [add_comm] using hden_plus_one
  have hratio_pos :
      0 < (x ^ 2 + (1 - δ) ^ 2) / (x ^ 2 + (1 + δ) ^ 2) :=
    div_pos hden_minus_one hden_plus_one
  have hu :
      -Real.log
          (Real.sqrt ((x ^ 2 + (1 - δ) ^ 2) / (x ^ 2 + (1 + δ) ^ 2))) =
        (1 / 2 : ℝ) *
          Real.log ((x ^ 2 + (δ + 1) ^ 2) / (x ^ 2 + (δ - 1) ^ 2)) := by
    have hminus_eq : x ^ 2 + (1 - δ) ^ 2 = x ^ 2 + (δ - 1) ^ 2 := by ring
    have hplus_eq : x ^ 2 + (1 + δ) ^ 2 = x ^ 2 + (δ + 1) ^ 2 := by ring
    rw [hminus_eq, hplus_eq]
    have hratio_pos' : 0 < (x ^ 2 + (δ - 1) ^ 2) / (x ^ 2 + (δ + 1) ^ 2) :=
      div_pos hden_minus_delta hden_plus_delta
    rw [Real.log_sqrt (le_of_lt hratio_pos')]
    rw [Real.log_div (ne_of_gt hden_minus_delta) (ne_of_gt hden_plus_delta)]
    rw [Real.log_div (ne_of_gt hden_plus_delta) (ne_of_gt hden_minus_delta)]
    ring
  have hcore :=
    xi_cayley_offset_defect_spectrum_bounds_pointwise x δ hδ0 hden_minus_delta
  rw [hu]
  constructor
  · calc
      (1 / 2 : ℝ) * (4 * δ / (x ^ 2 + (1 + δ) ^ 2)) =
          (2 * δ) / (x ^ 2 + (δ + 1) ^ 2) := by ring_nf
      _ ≤ (1 / 2 : ℝ) *
          Real.log ((x ^ 2 + (δ + 1) ^ 2) / (x ^ 2 + (δ - 1) ^ 2)) :=
        hcore.1
  · have hupper_alg :
        (2 * δ) / (x ^ 2 + (δ - 1) ^ 2) ≤
          ((1 + δ) ^ 2 / (2 * (1 - δ) ^ 2)) *
            (4 * δ / (x ^ 2 + (1 + δ) ^ 2)) := by
      have hone_sub_sq_pos : 0 < (1 - δ) ^ 2 := sq_pos_of_ne_zero hone_sub_ne
      have hbasic :
          (1 - δ) ^ 2 * (x ^ 2 + (1 + δ) ^ 2) ≤
            (1 + δ) ^ 2 * (x ^ 2 + (1 - δ) ^ 2) := by
        ring_nf
        nlinarith [sq_nonneg x, hδ0]
      have hrecip :
          1 / (x ^ 2 + (1 - δ) ^ 2) ≤
            (1 + δ) ^ 2 / ((1 - δ) ^ 2 * (x ^ 2 + (1 + δ) ^ 2)) := by
        rw [div_le_iff₀ hden_minus_one]
        calc
          (1 : ℝ) ≤
              ((1 + δ) ^ 2 * (x ^ 2 + (1 - δ) ^ 2)) /
                ((1 - δ) ^ 2 * (x ^ 2 + (1 + δ) ^ 2)) := by
            rw [le_div_iff₀ (mul_pos hone_sub_sq_pos hden_plus_one)]
            simpa [mul_assoc, mul_left_comm, mul_comm] using hbasic
          _ =
              (1 + δ) ^ 2 / ((1 - δ) ^ 2 * (x ^ 2 + (1 + δ) ^ 2)) *
                (x ^ 2 + (1 - δ) ^ 2) := by
            field_simp [ne_of_gt hden_plus_one, pow_ne_zero 2 hone_sub_ne]
      have hscaled := mul_le_mul_of_nonneg_left hrecip (by linarith : 0 ≤ 2 * δ)
      calc
        (2 * δ) / (x ^ 2 + (δ - 1) ^ 2) =
            (2 * δ) * (1 / (x ^ 2 + (1 - δ) ^ 2)) := by ring
        _ ≤ (2 * δ) *
            ((1 + δ) ^ 2 / ((1 - δ) ^ 2 * (x ^ 2 + (1 + δ) ^ 2))) :=
          hscaled
        _ = ((1 + δ) ^ 2 / (2 * (1 - δ) ^ 2)) *
            (4 * δ / (x ^ 2 + (1 + δ) ^ 2)) := by
          field_simp [ne_of_gt hden_plus_one, pow_ne_zero 2 hone_sub_ne]
          ring
    exact le_trans hcore.2 hupper_alg

end Omega.Zeta
