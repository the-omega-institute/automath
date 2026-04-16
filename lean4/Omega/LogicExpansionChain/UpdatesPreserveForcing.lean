import Omega.LogicExpansionChain.ForcingPersistence

namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper: explicit updates preserve forcing whenever realizations restrict along the
update and formulas are lifted pointwise.
    prop:logic-expansion-updates-preserve-forcing -/
theorem paper_logic_expansion_updates_preserve_forcing
    {ContextSmall ContextLarge ValSmall ValLarge Formula : Type}
    (Update :
      ForcingPersistence.InformationState ContextSmall ValSmall →
      ForcingPersistence.InformationState ContextLarge ValLarge → Prop)
    (restrict : ValLarge → ValSmall) (lift : Formula → Formula)
    (satisfiesSmall : ValSmall → Formula → Prop) (satisfiesLarge : ValLarge → Formula → Prop)
    (hUpdate : ∀ {p q}, Update p q → ∀ {s}, s ∈ q.realizations → restrict s ∈ p.realizations)
    (hlift : ∀ (s : ValLarge) (φ : Formula),
      satisfiesSmall (restrict s) φ → satisfiesLarge s (lift φ))
    {p : ForcingPersistence.InformationState ContextSmall ValSmall}
    {q : ForcingPersistence.InformationState ContextLarge ValLarge}
    {φ : Formula} (hstep : Update p q) (hp : ForcingPersistence.Forces satisfiesSmall p φ) :
    ForcingPersistence.Forces satisfiesLarge q (lift φ) := by
  refine ForcingPersistence.paper_logic_expansion_forcing_persistence_seeds
    restrict lift satisfiesSmall satisfiesLarge p q ?_ hlift hp
  intro s hs
  exact hUpdate hstep hs

end Omega.LogicExpansionChain
