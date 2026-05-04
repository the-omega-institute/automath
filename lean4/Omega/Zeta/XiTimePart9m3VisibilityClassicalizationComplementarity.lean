import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part9m3-visibility-classicalization-complementarity`. -/
theorem paper_xi_time_part9m3_visibility_classicalization_complementarity
    {α : Type*} [Fintype α] [Nonempty α] (m Bcl : ℕ) (p : α → ℝ)
    (pmax Col W : ℝ) (hp0 : ∀ x, 0 ≤ p x) (hsum : (∑ x, p x) = 1)
    (hmax : ∀ x, p x ≤ pmax) (hCol : Col = ∑ x, p x ^ 2) (hW : W = Col⁻¹)
    (hB : (2 : ℝ) ^ Bcl ≥ (2 : ℝ) ^ m * pmax) :
    (Bcl : ℝ) ≥ (m : ℝ) - Real.logb 2 W := by
  classical
  have hCol_le_pmax : Col ≤ pmax := by
    rw [hCol]
    calc
      (∑ x, p x ^ 2) ≤ ∑ x, pmax * p x := by
          refine Finset.sum_le_sum ?_
          intro x _hx
          have hpx0 : 0 ≤ p x := hp0 x
          have hpxmax : p x ≤ pmax := hmax x
          nlinarith [mul_le_mul_of_nonneg_right hpxmax hpx0]
      _ = pmax := by
          rw [← Finset.mul_sum, hsum, mul_one]
  have hCol_nonneg : 0 ≤ Col := by
    rw [hCol]
    exact Finset.sum_nonneg fun x _ => sq_nonneg (p x)
  have hCol_pos : 0 < Col := by
    have hsum_sq_pos : 0 < ∑ x, p x ^ 2 := by
      by_contra hnot
      have hsquares_zero : ∑ x, p x ^ 2 = 0 := by
        exact le_antisymm (not_lt.mp hnot) (Finset.sum_nonneg fun x _ => sq_nonneg (p x))
      have hp_zero : ∀ x, p x = 0 := by
        intro x
        have hx_nonneg : 0 ≤ p x ^ 2 := sq_nonneg (p x)
        have hx_le_sum : p x ^ 2 ≤ ∑ y, p y ^ 2 :=
          Finset.single_le_sum (fun y _ => sq_nonneg (p y)) (Finset.mem_univ x)
        have hx_sq_zero : p x ^ 2 = 0 := le_antisymm (by simpa [hsquares_zero] using hx_le_sum) hx_nonneg
        exact sq_eq_zero_iff.mp hx_sq_zero
      have : (∑ x, p x) = 0 := by simp [hp_zero]
      linarith
    simpa [hCol] using hsum_sq_pos
  have hW_pos : 0 < W := by
    rw [hW]
    positivity
  have hpowCol_le : (2 : ℝ) ^ m * Col ≤ (2 : ℝ) ^ Bcl := by
    calc
      (2 : ℝ) ^ m * Col ≤ (2 : ℝ) ^ m * pmax := by
        exact mul_le_mul_of_nonneg_left hCol_le_pmax (by positivity)
      _ ≤ (2 : ℝ) ^ Bcl := hB
  have hlog_le :
      Real.logb 2 ((2 : ℝ) ^ m * Col) ≤ Real.logb 2 ((2 : ℝ) ^ Bcl) := by
    exact Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (mul_pos (by positivity) hCol_pos) hpowCol_le
  have hlog_target :
      Real.logb 2 ((2 : ℝ) ^ m * Col) = (m : ℝ) - Real.logb 2 W := by
    rw [Real.logb_mul (pow_ne_zero m (by norm_num)) hCol_pos.ne']
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    rw [hW, Real.logb_inv]
    ring
  have hlog_B : Real.logb 2 ((2 : ℝ) ^ Bcl) = (Bcl : ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    ring
  linarith

end Omega.Zeta
