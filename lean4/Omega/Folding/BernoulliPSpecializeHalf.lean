import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.BayesKinkGeometry
import Omega.Folding.BernoulliPEndpointLdpRestated
import Omega.Folding.BernoulliPPressureQuartic

namespace Omega.Folding

/-- The Bernoulli-`p` closed forms specialize at `p = 1/2` to explicit rational values, while the
endpoint large-deviation rates collapse to logarithms with golden-ratio-type normalization. -/
theorem paper_fold_gauge_anomaly_bernoulli_p_specialize_half :
    (((1 / 2 : ℚ) ^ 2 * (3 - 2 * (1 / 2 : ℚ))) / (1 + (1 / 2 : ℚ) ^ 3) = 4 / 9) ∧
      ((((1 / 2 : ℚ) ^ 2 * (1 - (1 / 2 : ℚ)) *
            (21 * (1 / 2 : ℚ) ^ 5 - 6 * (1 / 2 : ℚ) ^ 4 + 14 * (1 / 2 : ℚ) ^ 3 -
              36 * (1 / 2 : ℚ) ^ 2 + 7 * (1 / 2 : ℚ) + 9)) /
          (((1 / 2 : ℚ) + 1) ^ 3 * (((1 / 2 : ℚ) ^ 2 - (1 / 2 : ℚ) + 1) ^ 3)) = 118 / 243) ∧
      (bernoulliPEndpointRateZero (1 / 2) = Real.log (4 / (1 + Real.sqrt 5))) ∧
      (bernoulliPEndpointRateOne (1 / 2) = Real.log 2)) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · have hinside : ((1 - (1 / 2 : ℝ)) * (1 + 3 * (1 / 2 : ℝ))) = 5 / 4 := by
      norm_num
    have hsqrt : Real.sqrt (5 / 4 : ℝ) = Real.sqrt 5 / 2 := by
      rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 5) (4 : ℝ)]
      norm_num
    have harg :
        (((1 - (1 / 2 : ℝ)) + Real.sqrt ((1 - (1 / 2 : ℝ)) * (1 + 3 * (1 / 2 : ℝ)))) / 2) =
          (1 + Real.sqrt 5) / 4 := by
      rw [hinside, hsqrt]
      ring
    rw [bernoulliPEndpointRateZero, harg, ← Real.log_inv]
    congr 1
    have hsqrt5_ne : (1 + Real.sqrt 5 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 5]
    field_simp [hsqrt5_ne]
  · rw [bernoulliPEndpointRateOne]
    have hval : ((1 / 2 : ℝ) ^ 2 * (1 - (1 / 2 : ℝ))) = 1 / 8 := by
      norm_num
    rw [hval]
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      calc
        Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ (3 : ℝ)) := by
          congr 1
          norm_num [Real.rpow_natCast]
        _ = 3 * Real.log 2 := by
          simpa using (Real.log_rpow (by positivity : 0 < (2 : ℝ)) (3 : ℝ))
    have hInv : (1 / 8 : ℝ) = (8 : ℝ)⁻¹ := by norm_num
    rw [hInv, Real.log_inv]
    nlinarith

end Omega.Folding
