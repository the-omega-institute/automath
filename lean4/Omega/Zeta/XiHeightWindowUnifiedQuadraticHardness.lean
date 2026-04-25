import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.Zeta.XiOptimalAllocationUnderProductBound
import Omega.Zeta.XiTimeHorizonProductLowerBound

namespace Omega.Zeta

/-- Boundary height-window reciprocal depth used by the unified quadratic lower-bound wrapper. -/
noncomputable def xi_height_window_unified_quadratic_hardness_Qmax (T δ0 : ℝ) : ℝ :=
  (T ^ 2 + (δ0 + 1) ^ 2) / (4 * δ0)

/-- Concrete package for the height-window formula and the product-budget hardness wrapper. -/
def xi_height_window_unified_quadratic_hardness_statement : Prop :=
  (∀ T δ0 : ℝ,
    xi_height_window_unified_quadratic_hardness_Qmax T δ0 =
      xi_time_horizon_product_lower_bound_Q T δ0) ∧
    (∀ D : xi_time_horizon_product_lower_bound_data,
      xi_time_horizon_product_lower_bound_Q D.γ D.δ ≤ (D.m : ℝ) * D.N) ∧
    (∀ T δ0 m N : ℝ, 0 ≤ m → 0 ≤ N →
      xi_height_window_unified_quadratic_hardness_Qmax T δ0 ≤ m * N →
        2 * Real.sqrt (xi_height_window_unified_quadratic_hardness_Qmax T δ0) ≤ m + N ∧
          Real.sqrt (xi_height_window_unified_quadratic_hardness_Qmax T δ0) ≤ max m N)

/-- Paper label: `thm:xi-height-window-unified-quadratic-hardness`. -/
theorem paper_xi_height_window_unified_quadratic_hardness
    (T delta0 Qmax budget : ℝ) (hdelta0 : 0 < delta0)
    (hQ : Qmax = (T ^ 2 + (1 + delta0) ^ 2) / (4 * delta0))
    (hBudget : Qmax ≤ budget) :
    (T ^ 2 + (1 + delta0) ^ 2) / (4 * delta0) ≤ budget := by
  have _ : 0 < delta0 := hdelta0
  simpa [hQ] using hBudget

/-- Combined wrapper for the height-window formula and product-budget lower-bound interface. -/
theorem xi_height_window_unified_quadratic_hardness_statement_verified :
    xi_height_window_unified_quadratic_hardness_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro T δ0
    rfl
  · intro D
    rcases paper_xi_time_horizon_product_lower_bound D with ⟨_, hQ, hbudget⟩
    simpa [hQ] using hbudget
  · intro T δ0 m N hm hN hQ
    exact paper_xi_optimal_allocation_under_product_bound hm hN hQ

end Omega.Zeta
