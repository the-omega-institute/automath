import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete strict lower bound for the near-1 `κ_∞` constant. The proof rewrites the logarithm
at the golden-ratio point as `log (1 + (√5 - 2))`, keeps the first two positive terms from the
mathlib series for `log (1 + x)`, and compares against rational bounds on `√5`.
`prop:near1-kappa-infty-c1-strict-ineq` -/
theorem paper_near1_kappa_infty_c1_strict_ineq :
    ((6 * Real.sqrt 5 - 5) / 250 : ℝ) < (3 / 4 : ℝ) * Real.log (2 / ((1 + Real.sqrt 5) / 2)) ^ 2 := by
  set x : ℝ := Real.sqrt 5 - 2
  set y : ℝ := x / (x + 2)
  have hsqrt5_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt5_pos : 0 < Real.sqrt 5 := by
    positivity
  have hsqrt5_nonneg : 0 ≤ Real.sqrt 5 := by
    positivity
  have hsqrt5_gt_two : (2 : ℝ) < Real.sqrt 5 := by
    nlinarith [hsqrt5_sq, hsqrt5_nonneg]
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    linarith
  have harg : 1 + x = 2 / ((1 + Real.sqrt 5) / 2) := by
    dsimp [x]
    field_simp [hsqrt5_pos.ne']
    nlinarith [hsqrt5_sq]
  have hy_eq : y = 1 - 2 / Real.sqrt 5 := by
    dsimp [y, x]
    field_simp [hsqrt5_pos.ne']
    ring
  have hsqrt5_gt_360_161 : (360 : ℝ) / 161 < Real.sqrt 5 := by
    have hbound_nonneg : 0 ≤ (360 : ℝ) / 161 := by
      positivity
    nlinarith [hsqrt5_sq, hbound_nonneg]
  have hsqrt5_lt_161_72 : Real.sqrt 5 < (161 : ℝ) / 72 := by
    have hbound_nonneg : 0 ≤ (161 : ℝ) / 72 := by
      positivity
    nlinarith [hsqrt5_sq, hsqrt5_nonneg, hbound_nonneg]
  have hy_lb : (19 / 180 : ℝ) ≤ y := by
    rw [hy_eq]
    have hdiv : (2 : ℝ) / Real.sqrt 5 ≤ (161 : ℝ) / 180 := by
      rw [div_le_iff₀ hsqrt5_pos]
      nlinarith [hsqrt5_gt_360_161]
    nlinarith
  let f : ℕ → ℝ := fun k => (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * y ^ (2 * k + 1)
  have hpartial :
      2 * y + (2 / 3 : ℝ) * y ^ 3 ≤ Real.log (1 + x) := by
    have hsum : Finset.sum (Finset.range 2) f ≤ Real.log (1 + x) := by
      exact
        sum_le_hasSum (Finset.range 2)
          (fun k _ => by
            have hy_nonneg : 0 ≤ y := by
              have : (0 : ℝ) ≤ 19 / 180 := by norm_num
              exact le_trans this hy_lb
            have hterm_nonneg :
                0 ≤ (2 : ℝ) * (1 / (2 * k + 1 : ℝ)) * y ^ (2 * k + 1) := by
              positivity
            simpa [f] using hterm_nonneg)
          (by simpa [f, y] using Real.hasSum_log_one_add hx_nonneg)
    have hsum' : 2 * y + 2 * ((2 + 1 : ℝ)⁻¹) * y ^ 3 ≤ Real.log (1 + x) := by
      simpa [f, Finset.sum_range_succ, y] using hsum
    nlinarith [hsum']
  have hrat_eq :
      (1853659 / 8748000 : ℝ) = 2 * (19 / 180 : ℝ) + (2 / 3 : ℝ) * (19 / 180 : ℝ) ^ 3 := by
    norm_num
  have hrat_le_partial : (1853659 / 8748000 : ℝ) ≤ 2 * y + (2 / 3 : ℝ) * y ^ 3 := by
    have hmono :
        2 * (19 / 180 : ℝ) + (2 / 3 : ℝ) * (19 / 180 : ℝ) ^ 3 ≤ 2 * y + (2 / 3 : ℝ) * y ^ 3 := by
      have hfactor :
          (2 * y + (2 / 3 : ℝ) * y ^ 3) -
              (2 * (19 / 180 : ℝ) + (2 / 3 : ℝ) * (19 / 180 : ℝ) ^ 3) =
            (y - 19 / 180) *
              ((2 / 3 : ℝ) *
                  (y ^ 2 + y * (19 / 180 : ℝ) + (19 / 180 : ℝ) ^ 2) +
                2) := by
        ring
      rw [← sub_nonneg, hfactor]
      have hy_diff_nonneg : 0 ≤ y - 19 / 180 := by
        linarith
      have hfactor_nonneg :
          0 ≤
            (2 / 3 : ℝ) * (y ^ 2 + y * (19 / 180 : ℝ) + (19 / 180 : ℝ) ^ 2) + 2 := by
        positivity
      exact mul_nonneg hy_diff_nonneg hfactor_nonneg
    simpa [hrat_eq] using hmono
  have hlog_lb : (1853659 / 8748000 : ℝ) ≤ Real.log (2 / ((1 + Real.sqrt 5) / 2)) := by
    have : (1853659 / 8748000 : ℝ) ≤ Real.log (1 + x) := le_trans hrat_le_partial hpartial
    simpa [harg] using this
  have hmain :
      ((6 * Real.sqrt 5 - 5) / 250 : ℝ) < (3 / 4 : ℝ) * (1853659 / 8748000 : ℝ) ^ 2 := by
    nlinarith [hsqrt5_lt_161_72]
  have hsquare :
      (3 / 4 : ℝ) * (1853659 / 8748000 : ℝ) ^ 2 ≤
        (3 / 4 : ℝ) * Real.log (2 / ((1 + Real.sqrt 5) / 2)) ^ 2 := by
    have hq_pos : (0 : ℝ) < 1853659 / 8748000 := by
      norm_num
    have hlog_nonneg : 0 ≤ Real.log (2 / ((1 + Real.sqrt 5) / 2)) := by
      exact le_trans hq_pos.le hlog_lb
    nlinarith
  exact lt_of_lt_of_le hmain hsquare

end Omega.Zeta
