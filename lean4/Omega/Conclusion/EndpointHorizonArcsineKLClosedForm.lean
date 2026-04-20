import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Endpoint-horizon arcsine density with support `(-a, a)`. -/
noncomputable def endpointHorizonDensity (a x : ℝ) : ℝ :=
  if |x| < a then 1 / (Real.pi * Real.sqrt (a ^ 2 - x ^ 2)) else 0

/-- Closed form of the endpoint-horizon KL functional obtained from the standard arcsine
substitution. -/
noncomputable def endpointHorizonKL (a b : ℝ) : ℝ :=
  Real.log ((b + Real.sqrt (b ^ 2 - a ^ 2)) / a)

/-- The endpoint-horizon arcsine KL divergence collapses to a single hyperbolic coordinate.
    thm:conclusion-endpoint-horizon-arcsine-kl-closed-form -/
theorem paper_conclusion_endpoint_horizon_arcsine_kl_closed_form (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) : endpointHorizonKL a b = Real.arcosh (b / a) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hnum_nonneg : 0 ≤ b ^ 2 - a ^ 2 := by
    nlinarith [hab, ha]
  have hsqrt :
      Real.sqrt ((b / a) ^ 2 - 1) = Real.sqrt (b ^ 2 - a ^ 2) / a := by
    have hdiv : (b / a) ^ 2 - 1 = (b ^ 2 - a ^ 2) / a ^ 2 := by
      field_simp [ha_ne]
    rw [hdiv, Real.sqrt_div hnum_nonneg (a ^ 2), Real.sqrt_sq_eq_abs, abs_of_pos ha]
  unfold endpointHorizonKL
  rw [Real.arcosh]
  congr 1
  calc
    (b + Real.sqrt (b ^ 2 - a ^ 2)) / a = b / a + Real.sqrt (b ^ 2 - a ^ 2) / a := by
      field_simp [ha_ne]
    _ = b / a + Real.sqrt ((b / a) ^ 2 - 1) := by
      rw [hsqrt]

end Omega.Conclusion
