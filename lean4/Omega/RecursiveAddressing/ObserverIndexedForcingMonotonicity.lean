import Omega.LogicExpansionChain.ForcingPersistence

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Observer-indexed forcing is monotone under refinement of realizations.
    prop:observer-indexed-forcing-monotonicity -/
theorem paper_recursive_addressing_observer_indexed_forcing_monotonicity
    {Context Val Formula : Type}
    (satisfies : Val → Formula → Prop)
    (p q : Omega.LogicExpansionChain.ForcingPersistence.InformationState Context Val)
    (href : q.realizations ⊆ p.realizations)
    {φ : Formula}
    (hp : Omega.LogicExpansionChain.ForcingPersistence.Forces satisfies p φ) :
    Omega.LogicExpansionChain.ForcingPersistence.Forces satisfies q φ := by
  simpa using
    (Omega.LogicExpansionChain.ForcingPersistence.paper_logic_expansion_forcing_persistence_seeds
      (restrict := id)
      (lift := id)
      (satisfiesSmall := satisfies)
      (satisfiesLarge := satisfies)
      (p := p)
      (q := q)
      (href := by
        intro σ hσ
        exact href hσ)
      (hlift := by
        intro σ ψ hσ
        simpa using hσ)
      (φ := φ)
      hp)

/-- Lowercase paper-label wrapper for observer-indexed forcing monotonicity.
    prop:observer-indexed-forcing-monotonicity -/
theorem paper_observer_indexed_forcing_monotonicity
    {Context Val Formula : Type}
    (satisfies : Val → Formula → Prop)
    (p q : Omega.LogicExpansionChain.ForcingPersistence.InformationState Context Val)
    (href : q.realizations ⊆ p.realizations)
    {φ : Formula}
    (hp : Omega.LogicExpansionChain.ForcingPersistence.Forces satisfies p φ) :
    Omega.LogicExpansionChain.ForcingPersistence.Forces satisfies q φ :=
  paper_recursive_addressing_observer_indexed_forcing_monotonicity satisfies p q href hp

end Omega.RecursiveAddressing
