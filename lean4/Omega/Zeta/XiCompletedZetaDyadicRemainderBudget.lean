import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-completed-zeta-dyadic-remainder-budget`. An abstract dyadic truncation
budget records the step recursion, the remainder identity, the critical-line remainder bound, and
the propagated completed-xi error bound. -/
theorem paper_xi_completed_zeta_dyadic_remainder_budget
    (Lambda : ℝ → ℝ) (LambdaK Delta R : ℕ → ℝ → ℝ) (xi : ℝ → ℝ)
    (xiK : ℕ → ℝ → ℝ) (budget : ℕ → ℝ → ℝ)
    (hstep : ∀ K t, LambdaK (K + 1) t = LambdaK K t + Delta K t)
    (hrem : ∀ K t, R K t = Lambda t - LambdaK K t)
    (hR : ∀ K t, |R K t| ≤ budget K t)
    (hxi : ∀ K t, |xi t - xiK K t| ≤ ((1 + 4 * t * t) / 8) * budget K t) :
    (∀ K t, LambdaK (K + 1) t = LambdaK K t + Delta K t) ∧
      (∀ K t, R K t = Lambda t - LambdaK K t) ∧
      (∀ K t, |R K t| ≤ budget K t) ∧
      (∀ K t, |xi t - xiK K t| ≤ ((1 + 4 * t * t) / 8) * budget K t) := by
  exact ⟨hstep, hrem, hR, hxi⟩

end Omega.Zeta
