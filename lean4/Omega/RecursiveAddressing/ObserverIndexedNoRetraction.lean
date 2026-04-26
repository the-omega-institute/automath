import Omega.RecursiveAddressing.ObserverIndexedForcingMonotonicity

namespace Omega.RecursiveAddressing

set_option maxHeartbeats 400000 in
/-- Refinement cannot retract a fact that was already forced at a coarser observer-indexed state.
    cor:observer-indexed-no-retraction -/
theorem paper_recursive_addressing_observer_indexed_no_retraction
    {Context Val Formula : Type}
    (satisfies : Val → Formula → Prop)
    (p q : Omega.LogicExpansionChain.ForcingPersistence.InformationState Context Val)
    (href : q.realizations ⊆ p.realizations)
    {φ : Formula}
    (hp : Omega.LogicExpansionChain.ForcingPersistence.Forces satisfies p φ) :
    Omega.LogicExpansionChain.ForcingPersistence.Forces satisfies q φ :=
  paper_recursive_addressing_observer_indexed_forcing_monotonicity
    satisfies p q href hp

/-- Lowercase paper-label wrapper for observer-indexed no-retraction.
    cor:observer-indexed-no-retraction -/
theorem paper_observer_indexed_no_retraction
    {Context Val Formula : Type}
    (satisfies : Val → Formula → Prop)
    (p q : Omega.LogicExpansionChain.ForcingPersistence.InformationState Context Val)
    (href : q.realizations ⊆ p.realizations)
    {φ : Formula}
    (hp : Omega.LogicExpansionChain.ForcingPersistence.Forces satisfies p φ) :
    Omega.LogicExpansionChain.ForcingPersistence.Forces satisfies q φ := by
  exact paper_recursive_addressing_observer_indexed_no_retraction satisfies p q href hp

end Omega.RecursiveAddressing
