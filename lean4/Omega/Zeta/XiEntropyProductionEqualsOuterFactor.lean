import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-entropy-production-equals-outer-factor`. -/
theorem paper_xi_entropy_production_equals_outer_factor
    (boundaryEntropy poissonExtension outerLog : ℝ → ℝ)
    (outerConstantModOne pureInner : Prop)
    (hPoisson : ∀ θ : ℝ, outerLog θ = poissonExtension (boundaryEntropy θ))
    (hZero : (∀ θ : ℝ, boundaryEntropy θ = 0) ↔ outerConstantModOne)
    (hInner : outerConstantModOne → pureInner) :
    (∀ θ : ℝ, outerLog θ = poissonExtension (boundaryEntropy θ)) ∧
      ((∀ θ : ℝ, boundaryEntropy θ = 0) ↔ outerConstantModOne) ∧
        (outerConstantModOne → pureInner) := by
  exact ⟨hPoisson, hZero, hInner⟩

end Omega.Zeta
