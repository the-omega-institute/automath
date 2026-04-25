import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-tqft-sphere-partition-function-s2`.
At genus zero, the genus partition-function formula specializes to the second moment. -/
theorem paper_conclusion_tqft_sphere_partition_function_s2 {X : Type*} [Fintype X]
    (d : X → ℕ) (Z : ℕ → ℕ) (hZ : ∀ g, Z g = ∑ x, d x ^ (g + 2)) :
    Z 0 = ∑ x, d x ^ 2 := by
  simpa using hZ 0

end Omega.Conclusion
