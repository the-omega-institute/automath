import Omega.LogicExpansionChain.ForcingPersistence

namespace Omega.LogicExpansionChain

open ForcingPersistence

/-- Ordinary semantic consequence, evaluated pointwise on realizations. -/
def PointwiseEntails {Val Formula : Type} (satisfies : Val → Formula → Prop)
    (Γ : Set Formula) (φ : Formula) : Prop :=
  ∀ ρ, (∀ ψ ∈ Γ, satisfies ρ ψ) → satisfies ρ φ

/-- Semantic consequence lifted from realizations to information states. -/
def StateEntails {Context Val Formula : Type} (satisfies : Val → Formula → Prop)
    (Γ : Set Formula) (φ : Formula) : Prop :=
  ∀ p : InformationState Context Val, (∀ ψ ∈ Γ, Forces satisfies p ψ) → Forces satisfies p φ

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: pointwise soundness lifts to state forcing.
    prop:lifted-pointwise-soundness -/
theorem paper_information_state_lifted_pointwise_soundness_seeds
    {Context Val Formula : Type}
    (satisfies : Val → Formula → Prop)
    (derivable : Set Formula → Formula → Prop)
    (hsound : ∀ Γ φ, derivable Γ φ → PointwiseEntails satisfies Γ φ)
    (Γ : Set Formula) (φ : Formula)
    (hΓ : derivable Γ φ) :
    StateEntails (Context := Context) satisfies Γ φ := by
  intro p hp ρ hρ
  exact hsound Γ φ hΓ ρ (fun ψ hψ => hp ψ hψ ρ hρ)

end Omega.LogicExpansionChain
