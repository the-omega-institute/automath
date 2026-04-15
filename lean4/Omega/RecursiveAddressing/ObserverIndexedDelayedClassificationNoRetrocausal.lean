import Omega.LogicExpansionChain.DelayedDecidabilityNoNewTruth

namespace Omega.RecursiveAddressing

open Omega.LogicExpansionChain.ForcingPersistence

set_option maxHeartbeats 400000 in
/-- Observer-indexed delayed classification refines the current information state without
rewriting the earlier object-level content: the past-indexed formula stays undecided at `p`,
and every realization seen after the update still restricts to one already compatible with `p`.
    prop:observer-indexed-delayed-classification-not-retrocausal -/
theorem paper_recursive_addressing_observer_indexed_delayed_classification_not_retrocausal
    {ContextSmall ContextLarge ValSmall ValLarge Formula : Type}
    (Update :
      InformationState ContextSmall ValSmall →
      InformationState ContextLarge ValLarge → Prop)
    (restrict : ValLarge → ValSmall)
    (lift neg : Formula → Formula)
    (satisfiesSmall : ValSmall → Formula → Prop)
    (satisfiesLarge : ValLarge → Formula → Prop)
    (hUpdate : ∀ {p q}, Update p q → ∀ {s}, s ∈ q.realizations → restrict s ∈ p.realizations)
    (hlift : ∀ (s : ValLarge) (φ : Formula),
      satisfiesSmall (restrict s) φ → satisfiesLarge s (lift φ))
    {p : InformationState ContextSmall ValSmall}
    {q : InformationState ContextLarge ValLarge}
    {φ : Formula}
    (hstep : Update p q)
    (hpUndecided :
      ¬ Forces satisfiesSmall p φ ∧ ¬ Forces satisfiesSmall p (neg φ))
    (hqDecides :
      Forces satisfiesLarge q (lift φ) ∨
        Forces satisfiesLarge q (lift (neg φ))) :
    (¬ Forces satisfiesSmall p φ ∧ ¬ Forces satisfiesSmall p (neg φ)) ∧
      (∀ {s}, s ∈ q.realizations → restrict s ∈ p.realizations) := by
  have hDelayed :=
    Omega.LogicExpansionChain.paper_logic_expansion_delayed_decidability_no_new_truth
      Update restrict lift neg satisfiesSmall satisfiesLarge hUpdate hlift
      hstep hpUndecided hqDecides
  exact ⟨hDelayed.1, hDelayed.2.2.2.2⟩

end Omega.RecursiveAddressing
