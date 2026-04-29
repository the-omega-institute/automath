import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

private lemma xi_foldbin_shannon_deficit_constant_closed_form_log_three_halves_upper :
    Real.log (3 / 2 : ℝ) < (41 / 100 : ℝ) := by
  have hupper :=
    Real.log_div_le_sum_range_add (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 2
  have hratio : ((1 + (1 / 5 : ℝ)) / (1 - (1 / 5 : ℝ))) = 3 / 2 := by
    norm_num
  rw [hratio] at hupper
  have hbound :
      2 *
          ((∑ i ∈ Finset.range 2,
              (1 / 5 : ℝ) ^ (2 * i + 1) / (2 * i + 1)) +
            (1 / 5 : ℝ) ^ (2 * 2 + 1) / (1 - (1 / 5 : ℝ) ^ 2)) <
        41 / 100 := by
    norm_num [Finset.sum_range_succ]
  nlinarith

private lemma xi_foldbin_shannon_deficit_constant_closed_form_log_sqrt5_upper :
    Real.log (Real.sqrt 5) < (41 / 50 : ℝ) := by
  have hsqrt_pos : 0 < (Real.sqrt 5 : ℝ) := by positivity
  have hsqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt_lt : (Real.sqrt 5 : ℝ) < 9 / 4 := by
    nlinarith [sq_nonneg ((Real.sqrt 5 : ℝ) - 9 / 4), hsqrt_sq]
  have hlog_lt : Real.log (Real.sqrt 5) < Real.log (9 / 4 : ℝ) :=
    Real.log_lt_log hsqrt_pos hsqrt_lt
  have hlog94 : Real.log (9 / 4 : ℝ) = 2 * Real.log (3 / 2 : ℝ) := by
    have hpos : 0 < (3 / 2 : ℝ) := by norm_num
    rw [show (9 / 4 : ℝ) = (3 / 2) * (3 / 2) by norm_num]
    rw [Real.log_mul hpos.ne' hpos.ne']
    ring
  have h32 := xi_foldbin_shannon_deficit_constant_closed_form_log_three_halves_upper
  nlinarith

private lemma xi_foldbin_shannon_deficit_constant_closed_form_log_phi_lower :
    (12 / 25 : ℝ) < Real.log Real.goldenRatio := by
  let x : ℝ := Real.sqrt 5 - 2
  have hsqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt_pos : 0 < (Real.sqrt 5 : ℝ) := by positivity
  have hx0 : 0 ≤ x := by
    dsimp [x]
    have h2 : (2 : ℝ) < Real.sqrt 5 := by nlinarith [hsqrt_sq, hsqrt_pos]
    linarith
  have hxlt : x < 1 := by
    dsimp [x]
    have hlt3 : (Real.sqrt 5 : ℝ) < 3 := by nlinarith [hsqrt_sq, hsqrt_pos]
    linarith
  have hlower := Real.sum_range_le_log_div (x := x) hx0 hxlt 2
  have hratio : ((1 + x) / (1 - x)) = Real.goldenRatio := by
    dsimp [x]
    rw [Real.goldenRatio]
    have hden : 1 - (Real.sqrt 5 - 2) ≠ 0 := by nlinarith [hsqrt_sq, hsqrt_pos]
    rw [div_eq_iff hden]
    field_simp
    ring_nf
    nlinarith [hsqrt_sq]
  rw [hratio] at hlower
  have hsum :
      (12 / 25 : ℝ) <
        2 * (∑ i ∈ Finset.range 2, x ^ (2 * i + 1) / (2 * i + 1)) := by
    dsimp [x]
    norm_num [Finset.sum_range_succ]
    nlinarith [hsqrt_sq, hsqrt_pos]
  nlinarith

private lemma xi_foldbin_shannon_deficit_constant_closed_form_coeff_lower :
    (43 / 25 : ℝ) < (3 * Real.goldenRatio - 1) / Real.sqrt 5 := by
  have hsqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt_pos : 0 < (Real.sqrt 5 : ℝ) := by positivity
  rw [Real.goldenRatio]
  field_simp [ne_of_gt hsqrt_pos]
  nlinarith [hsqrt_sq, hsqrt_pos]

private lemma xi_foldbin_shannon_deficit_constant_closed_form_positive :
    0 <
      ((3 * Real.goldenRatio - 1) / Real.sqrt 5) * Real.log Real.goldenRatio -
        (1 / 2 : ℝ) * Real.log 5 := by
  have hcoeff := xi_foldbin_shannon_deficit_constant_closed_form_coeff_lower
  have hlog := xi_foldbin_shannon_deficit_constant_closed_form_log_phi_lower
  have hlogsqrt := xi_foldbin_shannon_deficit_constant_closed_form_log_sqrt5_upper
  have hlogphi_pos : 0 < Real.log Real.goldenRatio :=
    Real.log_pos Real.one_lt_goldenRatio
  have hprod_left :
      (43 / 25 : ℝ) * (12 / 25) < (43 / 25 : ℝ) * Real.log Real.goldenRatio :=
    mul_lt_mul_of_pos_left hlog (by norm_num)
  have hprod_right :
      (43 / 25 : ℝ) * Real.log Real.goldenRatio <
        ((3 * Real.goldenRatio - 1) / Real.sqrt 5) * Real.log Real.goldenRatio :=
    mul_lt_mul_of_pos_right hcoeff hlogphi_pos
  have hprod :
      (43 / 25 : ℝ) * (12 / 25) <
        ((3 * Real.goldenRatio - 1) / Real.sqrt 5) * Real.log Real.goldenRatio :=
    lt_trans hprod_left hprod_right
  have hlog5_full : Real.log 5 = 2 * Real.log (Real.sqrt 5) := by
    have hsqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
      rw [Real.sq_sqrt]
      norm_num
    calc
      Real.log 5 = Real.log ((Real.sqrt 5 : ℝ) ^ 2) := by rw [hsqrt_sq]
      _ = 2 * Real.log (Real.sqrt 5) := by
        rw [Real.log_pow]
        norm_num
  have hlog5 : (1 / 2 : ℝ) * Real.log 5 = Real.log (Real.sqrt 5) := by
    rw [hlog5_full]
    ring
  rw [hlog5]
  nlinarith

/-- Paper label: `cor:xi-foldbin-shannon-deficit-constant-closed-form`. -/
theorem paper_xi_foldbin_shannon_deficit_constant_closed_form :
    ∃ C_KL : ℝ,
      C_KL =
          ((3 * Real.goldenRatio - 1) / Real.sqrt 5) * Real.log Real.goldenRatio -
            (1 / 2 : ℝ) * Real.log 5 ∧
        0 < C_KL := by
  exact ⟨_, rfl, xi_foldbin_shannon_deficit_constant_closed_form_positive⟩

end Omega.Zeta
