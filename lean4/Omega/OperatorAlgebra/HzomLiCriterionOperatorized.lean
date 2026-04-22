import Mathlib

namespace Omega.OperatorAlgebra

/-- Paper label: `prop:op-algebra-li-criterion-operatorized`.
If the Li-side sequence is the discrete second difference of `a`, then nonnegativity of the
shifted Li coefficients is exactly discrete convexity of `a`. -/
theorem paper_op_algebra_li_criterion_operatorized (a : ℕ → ℝ) (Li : ℕ → ℝ)
    (hLi : ∀ n : ℕ, Li (n + 1) = a (n + 2) - 2 * a (n + 1) + a n) :
    (∀ n : ℕ, 0 ≤ Li (n + 1)) ↔ ∀ n : ℕ, 0 ≤ a (n + 2) - 2 * a (n + 1) + a n := by
  constructor
  · intro h n
    simpa [hLi n] using h n
  · intro h n
    simpa [hLi n] using h n

end Omega.OperatorAlgebra
