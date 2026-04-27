import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Omega.Zeta

open Finset

lemma xi_gram_entropy_lower_bound_by_coherence_log_one_add_upper_nonneg {x : ℝ}
    (hx : 0 ≤ x) : Real.log (1 + x) ≤ x - x ^ 2 / (2 * (1 + x)) := by
  let y : ℝ := x / (x + 2)
  have hx2_pos : 0 < x + 2 := by linarith
  have hx2_ne : x + 2 ≠ 0 := ne_of_gt hx2_pos
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy_lt_one : y < 1 := by
    dsimp [y]
    rw [div_lt_one hx2_pos]
    linarith
  have hy_sq_lt_one : y ^ 2 < 1 := by
    nlinarith [sq_nonneg y, hy_nonneg, hy_lt_one]
  have hy_sq_ne : 1 - y ^ 2 ≠ 0 := by nlinarith
  have hlog :=
    Real.log_div_le_sum_range_add (x := y) hy_nonneg hy_lt_one 1
  have hsum :
      (∑ i ∈ range 1, y ^ (2 * i + 1) / (2 * i + 1)) = y := by
    simp
  have hbound :
      Real.log ((1 + y) / (1 - y)) ≤ 2 * (y + y ^ 3 / (1 - y ^ 2)) := by
    rw [hsum] at hlog
    nlinarith
  have harg : 1 + x = (1 + y) / (1 - y) := by
    dsimp [y]
    field_simp [hx2_ne]
    ring
  have halg : 2 * (y + y ^ 3 / (1 - y ^ 2)) = x - x ^ 2 / (2 * (1 + x)) := by
    have hx1_ne : 1 + x ≠ 0 := by positivity
    dsimp [y]
    field_simp [hx2_ne, hx1_ne, hy_sq_ne]
    field_simp [show (x + 2) ^ 2 - x ^ 2 ≠ 0 by nlinarith [hx]]
    ring
  calc
    Real.log (1 + x) = Real.log ((1 + y) / (1 - y)) := by rw [harg]
    _ ≤ 2 * (y + y ^ 3 / (1 - y ^ 2)) := hbound
    _ = x - x ^ 2 / (2 * (1 + x)) := halg

lemma xi_gram_entropy_lower_bound_by_coherence_scalar {x : ℝ} (hx : -1 < x) :
    x ^ 2 / (2 * (1 + |x|)) ≤ x - Real.log (1 + x) := by
  by_cases hx_nonneg : 0 ≤ x
  · have hlog :=
      xi_gram_entropy_lower_bound_by_coherence_log_one_add_upper_nonneg hx_nonneg
    rw [abs_of_nonneg hx_nonneg]
    linarith
  · have hx_nonpos : x ≤ 0 := le_of_not_ge hx_nonneg
    let y : ℝ := -x / (1 + x)
    have hx1_pos : 0 < 1 + x := by linarith
    have hx1_ne : 1 + x ≠ 0 := ne_of_gt hx1_pos
    have hx2_pos : 0 < x + 2 := by linarith
    have hy_nonneg : 0 ≤ y := by
      dsimp [y]
      exact div_nonneg (neg_nonneg.mpr hx_nonpos) hx1_pos.le
    have hy2_pos : 0 < y + 2 := by linarith
    have hlog_lower := Real.le_log_one_add_of_nonneg hy_nonneg
    have hlog_id : Real.log (1 + y) = -Real.log (1 + x) := by
      have hy_arg : 1 + y = (1 + x)⁻¹ := by
        dsimp [y]
        field_simp [hx1_ne]
        ring
      rw [hy_arg, Real.log_inv]
    have hneglog : 2 * y / (y + 2) ≤ -Real.log (1 + x) := by
      simpa [hlog_id] using hlog_lower
    have halg :
        x ^ 2 / (2 * (1 + |x|)) ≤ x + 2 * y / (y + 2) := by
      rw [abs_of_nonpos hx_nonpos]
      have hright : x + 2 * y / (y + 2) = x ^ 2 / (x + 2) := by
        dsimp [y]
        have hx1_nonzero : 1 + x ≠ 0 := ne_of_gt hx1_pos
        have hx2_nonzero : x + 2 ≠ 0 := ne_of_gt hx2_pos
        field_simp [hx1_nonzero, hx2_nonzero]
        field_simp [show -x + 2 * (1 + x) ≠ 0 by linarith]
        ring
      rw [hright]
      have hden_le : x + 2 ≤ 2 * (1 - x) := by linarith
      have hmain : x ^ 2 / (2 * (1 - x)) ≤ x ^ 2 / (x + 2) :=
        div_le_div_of_nonneg_left (sq_nonneg x) hx2_pos hden_le
      simpa [sub_eq_add_neg] using hmain
    linarith

/-- Paper label: `prop:xi-gram-entropy-lower-bound-by-coherence`. -/
theorem paper_xi_gram_entropy_lower_bound_by_coherence {κ : ℕ} (lambda : Fin κ → ℝ)
    (opNorm frob S : ℝ) (hgt : ∀ r, -1 < lambda r)
    (htrace : (∑ r, lambda r) = 0) (hop : ∀ r, |lambda r| ≤ opNorm)
    (hfrob : frob = ∑ r, (lambda r) ^ 2)
    (hS : S = ∑ r, (lambda r - Real.log (1 + lambda r))) :
    frob / (2 * (1 + opNorm)) ≤ S := by
  by_cases hκ : κ = 0
  · subst κ
    rw [hfrob, hS]
    simp
  · have hκ_pos : 0 < κ := Nat.pos_of_ne_zero hκ
    let r0 : Fin κ := ⟨0, hκ_pos⟩
    have hop_nonneg : 0 ≤ opNorm := (abs_nonneg (lambda r0)).trans (hop r0)
    have hden_op_pos : 0 < 2 * (1 + opNorm) := by positivity
    have hterm :
        ∀ r : Fin κ,
          (lambda r) ^ 2 / (2 * (1 + opNorm)) ≤
            lambda r - Real.log (1 + lambda r) := by
      intro r
      have hscalar :=
        xi_gram_entropy_lower_bound_by_coherence_scalar (x := lambda r) (hgt r)
      have hden_abs_pos : 0 < 2 * (1 + |lambda r|) := by positivity
      have hden_le : 2 * (1 + |lambda r|) ≤ 2 * (1 + opNorm) := by
        nlinarith [hop r]
      have hfrac :
          (lambda r) ^ 2 / (2 * (1 + opNorm)) ≤
            (lambda r) ^ 2 / (2 * (1 + |lambda r|)) :=
        div_le_div_of_nonneg_left (sq_nonneg (lambda r)) hden_abs_pos hden_le
      exact hfrac.trans hscalar
    have hsum_le :
        (∑ r, (lambda r) ^ 2 / (2 * (1 + opNorm))) ≤
          ∑ r, (lambda r - Real.log (1 + lambda r)) :=
      sum_le_sum fun r _ => hterm r
    calc
      frob / (2 * (1 + opNorm))
          = (∑ r, (lambda r) ^ 2) / (2 * (1 + opNorm)) := by rw [hfrob]
      _ = ∑ r, (lambda r) ^ 2 / (2 * (1 + opNorm)) := by
        simp [div_eq_mul_inv, sum_mul]
      _ ≤ ∑ r, (lambda r - Real.log (1 + lambda r)) := hsum_le
      _ = S := by rw [hS]

end Omega.Zeta
