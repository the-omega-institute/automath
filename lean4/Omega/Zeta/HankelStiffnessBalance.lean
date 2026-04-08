import Mathlib.Tactic

namespace Omega.Zeta

/-- Lower bound: `2 · max(a+t, b-t) ≥ a + b` for any `t`.
    thm:xi-hankel-stiffness-optimal-balance -/
theorem max_balance_lower_bound (a b t : ℤ) :
    2 * max (a + t) (b - t) ≥ a + b := by
  rcases le_or_gt (a + t) (b - t) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h.le]; linarith

/-- Equivalent form: `max(a+t, b-t) · 2 ≥ a + b`.
    thm:xi-hankel-stiffness-optimal-balance -/
theorem max_balance_ge_half (a b t : ℤ) :
    max (a + t) (b - t) * 2 ≥ a + b := by
  have := max_balance_lower_bound a b t
  linarith

/-- Optimal balance point: `t* = ⌊(b-a)/2⌋`.
    thm:xi-hankel-stiffness-optimal-balance -/
def optimalT (a b : ℤ) : ℤ := (b - a) / 2

/-- Upper bound at the optimal `t`: `max · 2 ≤ a + b + 1`.
    thm:xi-hankel-stiffness-optimal-balance -/
theorem max_at_optimal_t (a b : ℤ) :
    max (a + optimalT a b) (b - optimalT a b) * 2 ≤ a + b + 1 := by
  unfold optimalT
  omega

/-- Equality at the optimal `t` when `a + b` is even.
    thm:xi-hankel-stiffness-optimal-balance -/
theorem max_at_optimal_even (a b : ℤ) (h : (a + b) % 2 = 0) :
    max (a + optimalT a b) (b - optimalT a b) * 2 = a + b := by
  unfold optimalT
  omega

/-- Paper package: ξ Hankel stiffness optimal balance.
    thm:xi-hankel-stiffness-optimal-balance -/
theorem paper_xi_hankel_stiffness_optimal_balance :
    (∀ a b t : ℤ, 2 * max (a + t) (b - t) ≥ a + b) ∧
    (∀ a b t : ℤ, max (a + t) (b - t) * 2 ≥ a + b) ∧
    (∀ a b : ℤ, max (a + optimalT a b) (b - optimalT a b) * 2 ≤ a + b + 1) ∧
    (∀ a b : ℤ, (a + b) % 2 = 0 →
      max (a + optimalT a b) (b - optimalT a b) * 2 = a + b) :=
  ⟨max_balance_lower_bound,
   max_balance_ge_half,
   max_at_optimal_t,
   max_at_optimal_even⟩

end Omega.Zeta
