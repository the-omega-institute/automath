import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The semi-axis pair `(a, b)` determines the underlying integer parameter `N` because
`(a + b) / 2 = sqrt N`. This is the arithmetic core behind the elliptic externalization
completeness statement. -/
theorem paper_conclusion_jg_ellipse_arithmetic_invertibility_completeness {N1 N2 : ℕ}
    (ha : Real.sqrt N1 + (Real.sqrt N1)⁻¹ = Real.sqrt N2 + (Real.sqrt N2)⁻¹)
    (hb : Real.sqrt N1 - (Real.sqrt N1)⁻¹ = Real.sqrt N2 - (Real.sqrt N2)⁻¹) : N1 = N2 := by
  have hsqrt : (Real.sqrt N1 : ℝ) = Real.sqrt N2 := by
    linarith
  have hsq : (N1 : ℝ) = N2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N1), Real.sq_sqrt (Nat.cast_nonneg N2), hsqrt]
  exact Nat.cast_injective (R := ℝ) hsq

end Omega.Conclusion
