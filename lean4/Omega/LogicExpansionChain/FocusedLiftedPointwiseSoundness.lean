import Omega.LogicExpansionChain.LiftedPointwiseSoundness

namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Focused wrapper theorem for the APAL information-state soundness label.
    prop:lifted-pointwise-soundness -/
theorem paper_information_state_lifted_pointwise_soundness_focused_seeds
    {Context Val Formula : Type}
    (satisfies : Val → Formula → Prop)
    (derivable : Set Formula → Formula → Prop)
    (hsound : ∀ Γ φ, derivable Γ φ → PointwiseEntails satisfies Γ φ)
    (Γ : Set Formula) (φ : Formula)
    (hΓ : derivable Γ φ) :
    StateEntails (Context := Context) satisfies Γ φ :=
  paper_information_state_lifted_pointwise_soundness_seeds
    satisfies derivable hsound Γ φ hΓ

/-- Package wrapper matching the focused APAL publication label.
    prop:lifted-pointwise-soundness -/
theorem paper_information_state_lifted_pointwise_soundness_focused_package
    {Context Val Formula : Type}
    (satisfies : Val → Formula → Prop)
    (derivable : Set Formula → Formula → Prop)
    (hsound : ∀ Γ φ, derivable Γ φ → PointwiseEntails satisfies Γ φ)
    (Γ : Set Formula) (φ : Formula)
    (hΓ : derivable Γ φ) :
    StateEntails (Context := Context) satisfies Γ φ :=
  paper_information_state_lifted_pointwise_soundness_focused_seeds
    satisfies derivable hsound Γ φ hΓ

end Omega.LogicExpansionChain
