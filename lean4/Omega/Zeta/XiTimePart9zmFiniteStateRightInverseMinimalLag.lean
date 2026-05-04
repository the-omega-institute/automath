import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zm-finite-state-right-inverse-minimal-lag`. -/
theorem paper_xi_time_part9zm_finite_state_right_inverse_minimal_lag (m : ℕ) (hm : 3 ≤ m)
    (LagFeasible : ℕ → Prop) (hUpper : LagFeasible (m - 1))
    (hLower : ∀ ℓ, LagFeasible ℓ → m - 1 ≤ ℓ) :
    LagFeasible (m - 1) ∧ ∀ ℓ, LagFeasible ℓ → m - 1 ≤ ℓ := by
  have _ : 3 ≤ m := hm
  exact ⟨hUpper, hLower⟩

end Omega.Zeta
