import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

lemma xi_poisson_cauchy_kolmogorov_second_order_constant_bound_nonneg (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x ^ 2) ^ 2 ≤ 9 / (16 * Real.sqrt 3) := by
  have hs_pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have hs_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hden_pos : 0 < (1 + x ^ 2) ^ 2 := by positivity
  have hcoef_pos : 0 < 16 * Real.sqrt 3 := by positivity
  have hmain : 16 * Real.sqrt 3 * x ≤ 9 * (1 + x ^ 2) ^ 2 := by
    let u : ℝ := Real.sqrt 3 * x
    have hu_nonneg : 0 ≤ u := by positivity
    have hquad_nonneg : 0 ≤ u ^ 2 + 2 * u + 9 := by
      nlinarith [sq_nonneg u, hu_nonneg]
    have hfac : 0 ≤ (u - 1) ^ 2 * (u ^ 2 + 2 * u + 9) :=
      mul_nonneg (sq_nonneg _) hquad_nonneg
    have hpoly : 0 ≤ u ^ 4 + 6 * u ^ 2 - 16 * u + 9 := by
      convert hfac using 1
      ring
    have hu_eq : u = Real.sqrt 3 * x := rfl
    have hrel :
        u ^ 4 + 6 * u ^ 2 - 16 * u + 9 =
          9 * (1 + x ^ 2) ^ 2 - 16 * Real.sqrt 3 * x := by
      rw [hu_eq]
      have hs_four : (Real.sqrt 3) ^ 4 = (9 : ℝ) := by nlinarith [hs_sq]
      ring_nf
      rw [hs_sq, hs_four]
      ring
    nlinarith [hpoly, hrel]
  rw [div_le_div_iff₀ hden_pos hcoef_pos]
  nlinarith

theorem paper_xi_poisson_cauchy_kolmogorov_second_order_constant :
    (∀ y : ℝ, |y| / (1 + y ^ 2) ^ 2 ≤ 9 / (16 * Real.sqrt 3)) ∧
      (1 / Real.sqrt 3) / (1 + (1 / Real.sqrt 3) ^ 2) ^ 2 =
        9 / (16 * Real.sqrt 3) := by
  constructor
  · intro y
    simpa [sq_abs] using
      xi_poisson_cauchy_kolmogorov_second_order_constant_bound_nonneg |y| (abs_nonneg y)
  · have hs_ne : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)).ne'
    have hs_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    field_simp [hs_ne]
    nlinarith
