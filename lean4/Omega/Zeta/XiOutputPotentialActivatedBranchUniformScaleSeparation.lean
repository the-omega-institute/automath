import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-output-potential-activated-branch-uniform-scale-separation`. -/
theorem paper_xi_output_potential_activated_branch_uniform_scale_separation
    (G : ℂ → ℂ → ℂ) (lambdaAct : ℂ → ℂ) (eps0 c0 : ℝ) (heps0 : 0 < eps0)
    (hc0 : 0 < c0)
    (hunique :
      ∀ u lam : ℂ,
        ‖u - 1‖ < eps0 → (G lam u = 0 ∧ ‖lam‖ < c0 ↔ lam = lambdaAct u)) :
    ∃ eps c : ℝ,
      0 < eps ∧
        0 < c ∧
          ∀ u lam : ℂ, ‖u - 1‖ < eps → (G lam u = 0 ∧ ‖lam‖ < c ↔ lam = lambdaAct u) := by
  exact ⟨eps0, c0, heps0, hc0, hunique⟩

end Omega.Zeta
