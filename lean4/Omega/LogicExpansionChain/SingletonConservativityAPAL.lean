import Omega.LogicExpansionChain.FocusedSingletonConservativity

namespace Omega.LogicExpansionChain.SingletonConservativityAPAL

set_option maxHeartbeats 400000 in
/-- APAL publication wrapper for the singleton conservativity proposition.
    prop:singleton-conservativity -/
theorem paper_information_state_singleton_conservativity_apal
    {Val Formula : Type} (satisfies : Val → Formula → Prop)
    (ρ : Val) (φ : Formula) :
    (∀ σ ∈ ({ρ} : Set Val), satisfies σ φ) ↔ satisfies ρ φ :=
  Omega.LogicExpansionChain.FocusedSingletonConservativity.paper_information_state_singleton_conservativity_seeds
    satisfies ρ φ

end Omega.LogicExpansionChain.SingletonConservativityAPAL
