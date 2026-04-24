import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-integer-pressure-discrete-convexity-strict-bound`. -/
theorem paper_pom_integer_pressure_discrete_convexity_strict_bound
    (τ : ℕ → ℝ)
    (hconvex : ∀ q ≥ 1, 2 * τ q ≤ τ (q - 1) + τ (q + 1))
    (hstrict : 2 * τ 1 < τ 0 + τ 2)
    (hτ0 : τ 0 = Real.log Real.goldenRatio)
    (hτ1 : τ 1 = Real.log 2) :
    2 * Real.log 2 - Real.log Real.goldenRatio < τ 2 := by
  have hconvex1 : 2 * τ 1 ≤ τ 0 + τ 2 := hconvex 1 (by norm_num)
  rw [hτ0, hτ1] at hconvex1 hstrict
  linarith

end Omega.POM
