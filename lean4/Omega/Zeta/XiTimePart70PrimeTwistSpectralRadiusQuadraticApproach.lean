import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part70-prime-twist-spectral-radius-quadratic-approach`. -/
theorem paper_xi_time_part70_prime_twist_spectral_radius_quadratic_approach
    (rho : ℕ → ℝ) (lambda C : ℝ)
    (hquad :
      ∀ eps : ℝ, 0 < eps →
        ∃ P : ℕ, ∀ p : ℕ, P ≤ p → Nat.Prime p → Odd p →
          |(p : ℝ) ^ 2 * (1 - rho p / lambda) - C| < eps)
    (hmono :
      ∃ P : ℕ, ∀ p q : ℕ, P ≤ p → Nat.Prime p → Odd p → Nat.Prime q → Odd q →
        p < q → rho p < rho q ∧ rho q < lambda) :
    (∀ eps : ℝ, 0 < eps →
      ∃ P : ℕ, ∀ p : ℕ, P ≤ p → Nat.Prime p → Odd p →
        |(p : ℝ) ^ 2 * (1 - rho p / lambda) - C| < eps) ∧
      (∃ P : ℕ, ∀ p q : ℕ, P ≤ p → Nat.Prime p → Odd p → Nat.Prime q → Odd q →
        p < q → rho p < rho q ∧ rho q < lambda) := by
  exact ⟨hquad, hmono⟩

end Omega.Zeta
