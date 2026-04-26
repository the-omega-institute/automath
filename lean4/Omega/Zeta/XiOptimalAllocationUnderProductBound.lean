import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- Under a product lower bound, the additive and balanced costs are minimized at the square-root
scale.
    prop:xi-optimal-allocation-under-product-bound -/
theorem paper_xi_optimal_allocation_under_product_bound {m N Q : ℝ} (hm : 0 ≤ m) (hN : 0 ≤ N)
    (hQ : Q ≤ m * N) : 2 * Real.sqrt Q ≤ m + N ∧ Real.sqrt Q ≤ max m N := by
  have hsqrtQ_le : Real.sqrt Q ≤ Real.sqrt (m * N) := Real.sqrt_le_sqrt hQ
  have hsum :
      2 * (Real.sqrt m * Real.sqrt N) ≤ m + N := by
    nlinarith [sq_nonneg (Real.sqrt m - Real.sqrt N), Real.sq_sqrt hm, Real.sq_sqrt hN]
  have hmain : 2 * Real.sqrt Q ≤ m + N := by
    calc
      2 * Real.sqrt Q ≤ 2 * Real.sqrt (m * N) := by
        exact mul_le_mul_of_nonneg_left hsqrtQ_le (by positivity)
      _ = 2 * (Real.sqrt m * Real.sqrt N) := by rw [Real.sqrt_mul hm]
      _ ≤ m + N := hsum
  have hhalf : Real.sqrt Q ≤ (m + N) / 2 := by
    nlinarith [hmain]
  have hmax : (m + N) / 2 ≤ max m N := by
    have hmmax : m ≤ max m N := le_max_left _ _
    have hNmax : N ≤ max m N := le_max_right _ _
    nlinarith
  exact ⟨hmain, hhalf.trans hmax⟩

end Omega.Zeta
