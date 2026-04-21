import Omega.Zeta.XiNullStatisticalRadius

namespace Omega.Zeta

open scoped BigOperators
open Omega.POM

noncomputable section

section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Paper label: `cor:xi-null-micro-kl-window`. Rewriting the micro-level KL defect as the entropy
window gap identifies the admissible interval `[0, κ_m(π)]`, with the section lift realizing the
upper endpoint. -/
theorem paper_xi_null_micro_kl_window
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) (μ : FiberMicrostate d → ℝ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x) (hμ_nonneg : ∀ a, 0 ≤ μ a)
    (hπ_nonneg : ∀ x, 0 ≤ π x) (hμ_sum : Finset.univ.sum μ = 1)
    (hkl_nonneg : 0 ≤ klDiv μ (fiberUniformLift d π))
    (hkl_le_kappa : klDiv μ (fiberUniformLift d π) ≤ xiNullFiberKappa d π) :
    klDiv μ (fiberUniformLift d π) =
        xiNullFiberBaseEntropy π + xiNullFiberKappa d π - liftEntropy d μ ∧
      0 ≤ klDiv μ (fiberUniformLift d π) ∧
      klDiv μ (fiberUniformLift d π) ≤ xiNullFiberKappa d π ∧
      klDiv (xiNullFiberSectionLift d hd π) (fiberUniformLift d π) = xiNullFiberKappa d π := by
  rcases
      paper_xi_null_fiber_entropy_window d hd π μ hμ_marginal hμ_nonneg hπ_nonneg hμ_sum with
    ⟨hwindow, -, -, hsection⟩
  have hrewrite :
      klDiv μ (fiberUniformLift d π) =
        xiNullFiberBaseEntropy π + xiNullFiberKappa d π - liftEntropy d μ := by
    linarith
  exact ⟨hrewrite, hkl_nonneg, hkl_le_kappa, hsection⟩

end

end

end Omega.Zeta
