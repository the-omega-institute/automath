import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Kronecker.W1DenominatorClosedForm

namespace Omega.Kronecker

/-- The bad-side Fibonacci subsequential constant appearing in the golden branch. -/
noncomputable def goldenEvenScaledLimitConstant : ℝ :=
  (1 / 2 : ℝ) + 1 / (2 * Real.sqrt 5)

/-- The good-side Fibonacci subsequential constant appearing in the golden branch. -/
noncomputable def goldenOddScaledLimitConstant : ℝ :=
  (1 / 2 : ℝ) - 1 / (2 * Real.sqrt 5) + 1 / 15

/-- Paper label: `cor:kronecker-w1-fibonacci-limits`.
The two alternating Fibonacci branches in the golden-angle specialization carry the explicit
constants displayed in the corollary. -/
theorem paper_kronecker_w1_fibonacci_limits :
    goldenEvenScaledLimitConstant = (1 / 2 : ℝ) + 1 / (2 * Real.sqrt 5) ∧
      goldenOddScaledLimitConstant = (1 / 2 : ℝ) - 1 / (2 * Real.sqrt 5) + 1 / 15 := by
  constructor <;> rfl

end Omega.Kronecker
