import Omega.LogicExpansionChain.StateForcingPersistence

namespace Omega.LogicExpansionChain

/-- Publication wrapper for persistence of forcing in information states.
    prop:forcing-persistence -/
theorem paper_information_state_forcing_persistence_publication
    {ContextSmall ContextLarge ValSmall ValLarge Formula : Type}
    (restrict : ValLarge → ValSmall) (lift : Formula → Formula)
    (satisfiesSmall : ValSmall → Formula → Prop) (satisfiesLarge : ValLarge → Formula → Prop)
    (p : ForcingPersistence.InformationState ContextSmall ValSmall)
    (q : ForcingPersistence.InformationState ContextLarge ValLarge)
    (href : ∀ {σ}, σ ∈ q.realizations → restrict σ ∈ p.realizations)
    (hlift : ∀ (σ : ValLarge) (φ : Formula),
      satisfiesSmall (restrict σ) φ → satisfiesLarge σ (lift φ))
    {φ : Formula} (hp : ForcingPersistence.Forces satisfiesSmall p φ) :
    ForcingPersistence.Forces satisfiesLarge q (lift φ) :=
  paper_information_state_forcing_persistence_seeds
    restrict lift satisfiesSmall satisfiesLarge p q href hlift hp

end Omega.LogicExpansionChain
