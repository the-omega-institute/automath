import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-foldgauge-pi-buffon-quadratic-exponential-cost`. -/
theorem paper_conclusion_foldgauge_pi_buffon_quadratic_exponential_cost
    (N m : ℕ) (q C : ℝ) (hN : 0 < (N : ℝ)) (hC : 0 < C) (hq : 0 < q)
    (hrms : C / Real.sqrt (N : ℝ) ≤ q ^ m) :
    C ^ 2 / q ^ (2 * m) ≤ (N : ℝ) := by
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN
  have hqm_pos : 0 < q ^ m := pow_pos hq m
  have hq2m_pos : 0 < q ^ (2 * m) := pow_pos hq (2 * m)
  have hC_le : C ≤ q ^ m * Real.sqrt (N : ℝ) := by
    calc
      C = (C / Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) := by
        field_simp [ne_of_gt hsqrt_pos]
      _ ≤ q ^ m * Real.sqrt (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right hrms (le_of_lt hsqrt_pos)
  have hsq_le : C ^ 2 ≤ (q ^ m * Real.sqrt (N : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (C - q ^ m * Real.sqrt (N : ℝ))]
  have htarget_mul : C ^ 2 ≤ (N : ℝ) * q ^ (2 * m) := by
    have hsqrt_sq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (le_of_lt hN)
    calc
      C ^ 2 ≤ (q ^ m * Real.sqrt (N : ℝ)) ^ 2 := hsq_le
      _ = (N : ℝ) * q ^ (2 * m) := by
        rw [mul_pow, hsqrt_sq]
        ring
  exact (div_le_iff₀ hq2m_pos).2 (by
    exact htarget_mul)

end Omega.Conclusion
