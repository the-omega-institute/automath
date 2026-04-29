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

/-- Concrete data for the exact paper-label wrapper. -/
structure observer_indexed_delayed_classification_not_retrocausal_data where
  observer_indexed_delayed_classification_not_retrocausal_ContextSmall : Type
  observer_indexed_delayed_classification_not_retrocausal_ContextLarge : Type
  observer_indexed_delayed_classification_not_retrocausal_ValSmall : Type
  observer_indexed_delayed_classification_not_retrocausal_ValLarge : Type
  observer_indexed_delayed_classification_not_retrocausal_Formula : Type
  observer_indexed_delayed_classification_not_retrocausal_Update :
    InformationState
        observer_indexed_delayed_classification_not_retrocausal_ContextSmall
        observer_indexed_delayed_classification_not_retrocausal_ValSmall →
      InformationState
        observer_indexed_delayed_classification_not_retrocausal_ContextLarge
        observer_indexed_delayed_classification_not_retrocausal_ValLarge → Prop
  observer_indexed_delayed_classification_not_retrocausal_restrict :
    observer_indexed_delayed_classification_not_retrocausal_ValLarge →
      observer_indexed_delayed_classification_not_retrocausal_ValSmall
  observer_indexed_delayed_classification_not_retrocausal_lift :
    observer_indexed_delayed_classification_not_retrocausal_Formula →
      observer_indexed_delayed_classification_not_retrocausal_Formula
  observer_indexed_delayed_classification_not_retrocausal_neg :
    observer_indexed_delayed_classification_not_retrocausal_Formula →
      observer_indexed_delayed_classification_not_retrocausal_Formula
  observer_indexed_delayed_classification_not_retrocausal_satisfiesSmall :
    observer_indexed_delayed_classification_not_retrocausal_ValSmall →
      observer_indexed_delayed_classification_not_retrocausal_Formula → Prop
  observer_indexed_delayed_classification_not_retrocausal_satisfiesLarge :
    observer_indexed_delayed_classification_not_retrocausal_ValLarge →
      observer_indexed_delayed_classification_not_retrocausal_Formula → Prop
  observer_indexed_delayed_classification_not_retrocausal_p :
    InformationState
      observer_indexed_delayed_classification_not_retrocausal_ContextSmall
      observer_indexed_delayed_classification_not_retrocausal_ValSmall
  observer_indexed_delayed_classification_not_retrocausal_q :
    InformationState
      observer_indexed_delayed_classification_not_retrocausal_ContextLarge
      observer_indexed_delayed_classification_not_retrocausal_ValLarge
  observer_indexed_delayed_classification_not_retrocausal_phi :
    observer_indexed_delayed_classification_not_retrocausal_Formula
  observer_indexed_delayed_classification_not_retrocausal_hUpdate :
    ∀ {p q},
      observer_indexed_delayed_classification_not_retrocausal_Update p q →
        ∀ {s},
          s ∈ q.realizations →
            observer_indexed_delayed_classification_not_retrocausal_restrict s ∈
              p.realizations
  observer_indexed_delayed_classification_not_retrocausal_hlift :
    ∀ (s : observer_indexed_delayed_classification_not_retrocausal_ValLarge)
      (φ : observer_indexed_delayed_classification_not_retrocausal_Formula),
      observer_indexed_delayed_classification_not_retrocausal_satisfiesSmall
          (observer_indexed_delayed_classification_not_retrocausal_restrict s) φ →
        observer_indexed_delayed_classification_not_retrocausal_satisfiesLarge s
          (observer_indexed_delayed_classification_not_retrocausal_lift φ)
  observer_indexed_delayed_classification_not_retrocausal_hstep :
    observer_indexed_delayed_classification_not_retrocausal_Update
      observer_indexed_delayed_classification_not_retrocausal_p
      observer_indexed_delayed_classification_not_retrocausal_q
  observer_indexed_delayed_classification_not_retrocausal_hpUndecided :
    ¬ Forces observer_indexed_delayed_classification_not_retrocausal_satisfiesSmall
        observer_indexed_delayed_classification_not_retrocausal_p
        observer_indexed_delayed_classification_not_retrocausal_phi ∧
      ¬ Forces observer_indexed_delayed_classification_not_retrocausal_satisfiesSmall
        observer_indexed_delayed_classification_not_retrocausal_p
        (observer_indexed_delayed_classification_not_retrocausal_neg
          observer_indexed_delayed_classification_not_retrocausal_phi)
  observer_indexed_delayed_classification_not_retrocausal_hqDecides :
    Forces observer_indexed_delayed_classification_not_retrocausal_satisfiesLarge
        observer_indexed_delayed_classification_not_retrocausal_q
        (observer_indexed_delayed_classification_not_retrocausal_lift
          observer_indexed_delayed_classification_not_retrocausal_phi) ∨
      Forces observer_indexed_delayed_classification_not_retrocausal_satisfiesLarge
        observer_indexed_delayed_classification_not_retrocausal_q
        (observer_indexed_delayed_classification_not_retrocausal_lift
          (observer_indexed_delayed_classification_not_retrocausal_neg
            observer_indexed_delayed_classification_not_retrocausal_phi))

namespace observer_indexed_delayed_classification_not_retrocausal_data

def statement (D : observer_indexed_delayed_classification_not_retrocausal_data) : Prop :=
  (¬ Forces D.observer_indexed_delayed_classification_not_retrocausal_satisfiesSmall
      D.observer_indexed_delayed_classification_not_retrocausal_p
      D.observer_indexed_delayed_classification_not_retrocausal_phi ∧
    ¬ Forces D.observer_indexed_delayed_classification_not_retrocausal_satisfiesSmall
      D.observer_indexed_delayed_classification_not_retrocausal_p
      (D.observer_indexed_delayed_classification_not_retrocausal_neg
        D.observer_indexed_delayed_classification_not_retrocausal_phi)) ∧
    (∀ {s},
      s ∈ D.observer_indexed_delayed_classification_not_retrocausal_q.realizations →
        D.observer_indexed_delayed_classification_not_retrocausal_restrict s ∈
          D.observer_indexed_delayed_classification_not_retrocausal_p.realizations)

end observer_indexed_delayed_classification_not_retrocausal_data

open observer_indexed_delayed_classification_not_retrocausal_data

set_option maxHeartbeats 400000 in
/-- Paper label: `prop:observer-indexed-delayed-classification-not-retrocausal`. -/
theorem paper_observer_indexed_delayed_classification_not_retrocausal
    (D : observer_indexed_delayed_classification_not_retrocausal_data) : D.statement := by
  exact
    paper_recursive_addressing_observer_indexed_delayed_classification_not_retrocausal
      D.observer_indexed_delayed_classification_not_retrocausal_Update
      D.observer_indexed_delayed_classification_not_retrocausal_restrict
      D.observer_indexed_delayed_classification_not_retrocausal_lift
      D.observer_indexed_delayed_classification_not_retrocausal_neg
      D.observer_indexed_delayed_classification_not_retrocausal_satisfiesSmall
      D.observer_indexed_delayed_classification_not_retrocausal_satisfiesLarge
      D.observer_indexed_delayed_classification_not_retrocausal_hUpdate
      D.observer_indexed_delayed_classification_not_retrocausal_hlift
      D.observer_indexed_delayed_classification_not_retrocausal_hstep
      D.observer_indexed_delayed_classification_not_retrocausal_hpUndecided
      D.observer_indexed_delayed_classification_not_retrocausal_hqDecides

end Omega.RecursiveAddressing
