import Omega.LogicExpansionChain.SingletonConservativity

namespace Omega.LogicExpansionChain.FocusedSingletonConservativity

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: forcing over a singleton information state reduces to point semantics.
    prop:singleton-conservativity -/
theorem paper_information_state_singleton_conservativity_seeds
    {Val Formula : Type} (satisfies : Val → Formula → Prop)
    (ρ : Val) (φ : Formula) :
    (∀ σ ∈ ({ρ} : Set Val), satisfies σ φ) ↔ satisfies ρ φ :=
  Omega.LogicExpansionChain.SingletonConservativity.paper_logic_expansion_singleton_conservativity_seeds
    satisfies ρ φ

/-- Wrapper theorem matching the focused-publication label.
    prop:singleton-conservativity -/
theorem paper_information_state_singleton_conservativity_package
    {Val Formula : Type} (satisfies : Val → Formula → Prop)
    (ρ : Val) (φ : Formula) :
    (∀ σ ∈ ({ρ} : Set Val), satisfies σ φ) ↔ satisfies ρ φ :=
  paper_information_state_singleton_conservativity_seeds satisfies ρ φ

end Omega.LogicExpansionChain.FocusedSingletonConservativity
