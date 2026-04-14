import Mathlib.Tactic

namespace Omega.LogicExpansionChain.FocusedConservativeComposition

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: conservative extensions compose by composing forgetful maps and
state projections.
    prop:conservative-composition -/
theorem paper_conservative_extension_composition_seeds
    {Formula M₀ M₁ M₂ S₀ S₁ S₂ : Type}
    (forces₀ : M₀ → S₀ → Formula → Prop)
    (forces₁ : M₁ → S₁ → Formula → Prop)
    (forces₂ : M₂ → S₂ → Formula → Prop)
    (forget₁₀ : M₁ → M₀) (forget₂₁ : M₂ → M₁)
    (project₁₀ : M₁ → S₁ → S₀)
    (project₂₁ : M₂ → S₂ → S₁)
    (h₁₀ : ∀ (φ : Formula) (M : M₁) (p : S₁),
      forces₁ M p φ ↔ forces₀ (forget₁₀ M) (project₁₀ M p) φ)
    (h₂₁ : ∀ (φ : Formula) (M : M₂) (p : S₂),
      forces₂ M p φ ↔ forces₁ (forget₂₁ M) (project₂₁ M p) φ) :
    ∀ (φ : Formula) (M : M₂) (p : S₂),
      forces₂ M p φ ↔
        forces₀ (forget₁₀ (forget₂₁ M))
          (project₁₀ (forget₂₁ M) (project₂₁ M p)) φ := by
  intro φ M p
  exact (h₂₁ φ M p).trans (h₁₀ φ (forget₂₁ M) (project₂₁ M p))

/-- Wrapper theorem matching the focused-publication label.
    prop:conservative-composition -/
theorem paper_conservative_extension_composition_package
    {Formula M₀ M₁ M₂ S₀ S₁ S₂ : Type}
    (forces₀ : M₀ → S₀ → Formula → Prop)
    (forces₁ : M₁ → S₁ → Formula → Prop)
    (forces₂ : M₂ → S₂ → Formula → Prop)
    (forget₁₀ : M₁ → M₀) (forget₂₁ : M₂ → M₁)
    (project₁₀ : M₁ → S₁ → S₀)
    (project₂₁ : M₂ → S₂ → S₁)
    (h₁₀ : ∀ (φ : Formula) (M : M₁) (p : S₁),
      forces₁ M p φ ↔ forces₀ (forget₁₀ M) (project₁₀ M p) φ)
    (h₂₁ : ∀ (φ : Formula) (M : M₂) (p : S₂),
      forces₂ M p φ ↔ forces₁ (forget₂₁ M) (project₂₁ M p) φ) :
    ∀ (φ : Formula) (M : M₂) (p : S₂),
      forces₂ M p φ ↔
        forces₀ (forget₁₀ (forget₂₁ M))
          (project₁₀ (forget₂₁ M) (project₂₁ M p)) φ :=
  paper_conservative_extension_composition_seeds
    forces₀ forces₁ forces₂ forget₁₀ forget₂₁ project₁₀ project₂₁ h₁₀ h₂₁

end Omega.LogicExpansionChain.FocusedConservativeComposition
