import Omega.LogicExpansionChain.ForcingPersistence

namespace Omega.LogicExpansionChain

open ForcingPersistence

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: lower-layer forcing is exactly the flat team-style universal reading.
    prop:flat-team-reading -/
theorem paper_information_state_flat_team_reading_seeds
    {Context Val Formula : Type}
    (satisfies : Val → Formula → Prop)
    (p : InformationState Context Val) (φ : Formula) :
    Forces satisfies p φ ↔ ∀ ρ ∈ p.realizations, satisfies ρ φ :=
  Iff.rfl

/-- Wrapper theorem matching the focused APAL publication label.
    prop:flat-team-reading -/
theorem paper_information_state_flat_team_reading_package
    {Context Val Formula : Type}
    (satisfies : Val → Formula → Prop)
    (p : InformationState Context Val) (φ : Formula) :
    Forces satisfies p φ ↔ ∀ ρ ∈ p.realizations, satisfies ρ φ :=
  paper_information_state_flat_team_reading_seeds satisfies p φ

end Omega.LogicExpansionChain
