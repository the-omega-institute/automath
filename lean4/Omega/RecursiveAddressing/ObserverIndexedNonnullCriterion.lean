import Mathlib.Tactic

namespace Omega.RecursiveAddressing.ObserverIndexedNonnullCriterion

/-- Paper-facing local-section form of the non-`NULL` criterion.
    cor:observer-indexed-nonnull-criterion -/
theorem paper_observer_indexed_nonnull_criterion {State Address Section : Type*}
    (A : State → Set Address) (Γ : State → Address → Set Section)
    (nonnull : State → Address → Prop)
    (hnonnull : ∀ p a, nonnull p a ↔ a ∈ A p ∧ (Γ p a).Nonempty)
    (p : State) (a : Address) :
    nonnull p a ↔ a ∈ A p ∧ (Γ p a).Nonempty := by
  exact hnonnull p a

end Omega.RecursiveAddressing.ObserverIndexedNonnullCriterion
