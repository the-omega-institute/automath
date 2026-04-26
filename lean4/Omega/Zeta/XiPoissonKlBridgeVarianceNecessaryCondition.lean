import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-poisson-kl-bridge-variance-necessary-condition`. -/
theorem paper_xi_poisson_kl_bridge_variance_necessary_condition
    (ConvergesToZero : (ℕ → ℝ) → Prop) (KL ZetaDefect : ℕ → ℝ) (RH : Prop)
    (hKLZero : ConvergesToZero KL)
    (hBridge : ConvergesToZero KL → ConvergesToZero ZetaDefect)
    (hCriterion : ConvergesToZero ZetaDefect → RH) :
    RH := by
  exact hCriterion (hBridge hKLZero)

end Omega.Zeta
