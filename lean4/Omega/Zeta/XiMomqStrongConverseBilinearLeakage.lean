import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-momq-strong-converse-bilinear-leakage`. -/
theorem paper_xi_momq_strong_converse_bilinear_leakage
    (multiRoundLeak : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (q Γ h : ℝ)
    (hstrong : ∀ gap budget, n * max (gap - budget) 0 ≤ multiRoundLeak n gap budget) :
    n * max (q * Γ - h) 0 ≤ multiRoundLeak n (q * Γ) h := by
  exact hstrong (q * Γ) h

end Omega.Zeta
