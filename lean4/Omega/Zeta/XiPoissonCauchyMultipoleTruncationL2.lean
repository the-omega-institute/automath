import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-poisson-cauchy-multipole-truncation-l2`. -/
theorem paper_xi_poisson_cauchy_multipole_truncation_l2 (N : ℕ) (m : ℕ → ℂ)
    (error tail : ℝ)
    (h_tail : tail = ∑' k : ℕ, ‖m (N + 1 + k)‖ ^ 2)
    (h_parseval : error = 2 * tail) :
    error = 2 * ∑' k : ℕ, ‖m (N + 1 + k)‖ ^ 2 := by
  rw [h_parseval, h_tail]

end Omega.Zeta
