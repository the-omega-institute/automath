import Omega.LogicExpansionChain.UpdatesPreserveForcing

namespace Omega.LogicExpansionChain

open ForcingPersistence

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper: if a formula is undecided at `p` and decided after an update `p ↝ q`,
then the update preserves any truth that was already forced at `p`; the only structural change is
that `q` keeps a smaller realization family.
    prop:logic-expansion-delayed-decidability-no-new-truth -/
theorem paper_logic_expansion_delayed_decidability_no_new_truth
    {ContextSmall ContextLarge ValSmall ValLarge Formula : Type}
    (Update :
      InformationState ContextSmall ValSmall →
      InformationState ContextLarge ValLarge → Prop)
    (restrict : ValLarge → ValSmall) (lift : Formula → Formula) (neg : Formula → Formula)
    (satisfiesSmall : ValSmall → Formula → Prop) (satisfiesLarge : ValLarge → Formula → Prop)
    (hUpdate : ∀ {p q}, Update p q → ∀ {s}, s ∈ q.realizations → restrict s ∈ p.realizations)
    (hlift : ∀ (s : ValLarge) (φ : Formula),
      satisfiesSmall (restrict s) φ → satisfiesLarge s (lift φ))
    {p : InformationState ContextSmall ValSmall}
    {q : InformationState ContextLarge ValLarge}
    {φ : Formula}
    (hstep : Update p q)
    (hpUndecided : ¬ Forces satisfiesSmall p φ ∧ ¬ Forces satisfiesSmall p (neg φ))
    (hqDecides :
      Forces satisfiesLarge q (lift φ) ∨ Forces satisfiesLarge q (lift (neg φ))) :
    (¬ Forces satisfiesSmall p φ ∧ ¬ Forces satisfiesSmall p (neg φ)) ∧
    (Forces satisfiesSmall p φ → Forces satisfiesLarge q (lift φ)) ∧
    (Forces satisfiesSmall p (neg φ) → Forces satisfiesLarge q (lift (neg φ))) ∧
    (Forces satisfiesLarge q (lift φ) ∨ Forces satisfiesLarge q (lift (neg φ))) ∧
    (∀ {s}, s ∈ q.realizations → restrict s ∈ p.realizations) := by
  refine ⟨hpUndecided, ?_, ?_, hqDecides, ?_⟩
  · intro hp
    exact paper_logic_expansion_updates_preserve_forcing
      Update restrict lift satisfiesSmall satisfiesLarge hUpdate hlift hstep hp
  · intro hpNeg
    exact paper_logic_expansion_updates_preserve_forcing
      Update restrict lift satisfiesSmall satisfiesLarge hUpdate hlift hstep hpNeg
  · intro s hs
    exact hUpdate hstep hs

end Omega.LogicExpansionChain
