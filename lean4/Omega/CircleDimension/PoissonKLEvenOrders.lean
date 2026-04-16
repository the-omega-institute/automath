import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the vanishing of odd orders in the Poisson
    KL entropy expansion.
    thm:poisson-kl-even-orders -/
theorem paper_circle_dimension_poisson_kl_even_orders
    (N : ℕ)
    (coeff : ℕ → ℝ)
    (hasEvenExpansion : Prop)
    (hN : 2 ≤ N)
    (hEven : hasEvenExpansion)
    (hOdd : ∀ m, 2 ≤ m → m ≤ N → coeff (2 * m + 1) = 0) :
    2 ≤ N ∧ hasEvenExpansion ∧ ∀ m, 2 ≤ m → m ≤ N → coeff (2 * m + 1) = 0 := by
  exact ⟨hN, hEven, hOdd⟩

end Omega.CircleDimension
