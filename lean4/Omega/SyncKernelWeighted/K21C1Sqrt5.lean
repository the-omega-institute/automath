import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:k21-c1-sqrt5`. -/
theorem paper_k21_c1_sqrt5 (c1 «λ0» : ℝ) (hlambda0 : «λ0» = Real.goldenRatio)
    (hc1 : c1 / «λ0» = 3 - Real.goldenRatio) : c1 = Real.sqrt 5 := by
  rw [hlambda0] at hc1
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hc1' : c1 = Real.goldenRatio * (3 - Real.goldenRatio) := by
    calc
      c1 = (3 - Real.goldenRatio) * Real.goldenRatio := (div_eq_iff hphi_ne).mp hc1
      _ = Real.goldenRatio * (3 - Real.goldenRatio) := by ring
  have hc1'' : c1 = 2 * Real.goldenRatio - 1 := by
    calc
      c1 = Real.goldenRatio * (3 - Real.goldenRatio) := hc1'
      _ = 3 * Real.goldenRatio - Real.goldenRatio ^ 2 := by ring
      _ = 2 * Real.goldenRatio - 1 := by nlinarith [Real.goldenRatio_sq]
  have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hsqrt5_nonneg : 0 ≤ (Real.sqrt 5 : ℝ) := by positivity
  rw [hc1'', Real.goldenRatio]
  nlinarith [hsqrt5_sq, hsqrt5_nonneg]

end Omega.SyncKernelWeighted
