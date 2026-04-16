import Mathlib.Tactic

namespace Omega.LogicExpansionChain.ForcingPersistence

/-- A state carries a context together with the valuations still compatible with it. -/
structure InformationState (Context Val : Type) where
  context : Context
  realizations : Set Val

/-- A formula is forced at a state when it holds for every compatible valuation. -/
def Forces {Context Val Formula : Type} (satisfies : Val → Formula → Prop)
    (p : InformationState Context Val) (φ : Formula) : Prop :=
  ∀ ρ ∈ p.realizations, satisfies ρ φ

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: forcing is persistent under state refinement and formula lifting.
    prop:logic-expansion-forcing-persistence -/
theorem paper_logic_expansion_forcing_persistence_seeds
    {ContextSmall ContextLarge ValSmall ValLarge Formula : Type}
    (restrict : ValLarge → ValSmall) (lift : Formula → Formula)
    (satisfiesSmall : ValSmall → Formula → Prop) (satisfiesLarge : ValLarge → Formula → Prop)
    (p : InformationState ContextSmall ValSmall) (q : InformationState ContextLarge ValLarge)
    (href : ∀ {σ}, σ ∈ q.realizations → restrict σ ∈ p.realizations)
    (hlift : ∀ (σ : ValLarge) (φ : Formula),
      satisfiesSmall (restrict σ) φ → satisfiesLarge σ (lift φ))
    {φ : Formula} (hp : Forces satisfiesSmall p φ) :
    Forces satisfiesLarge q (lift φ) := by
  intro σ hσ
  exact hlift σ φ (hp (restrict σ) (href hσ))

/-- Wrapper theorem matching the paper-facing package name.
    prop:logic-expansion-forcing-persistence -/
theorem paper_logic_expansion_forcing_persistence_package
    {ContextSmall ContextLarge ValSmall ValLarge Formula : Type}
    (restrict : ValLarge → ValSmall) (lift : Formula → Formula)
    (satisfiesSmall : ValSmall → Formula → Prop) (satisfiesLarge : ValLarge → Formula → Prop)
    (p : InformationState ContextSmall ValSmall) (q : InformationState ContextLarge ValLarge)
    (href : ∀ {σ}, σ ∈ q.realizations → restrict σ ∈ p.realizations)
    (hlift : ∀ (σ : ValLarge) (φ : Formula),
      satisfiesSmall (restrict σ) φ → satisfiesLarge σ (lift φ))
    {φ : Formula} (hp : Forces satisfiesSmall p φ) :
    Forces satisfiesLarge q (lift φ) :=
  paper_logic_expansion_forcing_persistence_seeds
    restrict lift satisfiesSmall satisfiesLarge p q href hlift hp

/-- Unsuffixed paper-facing wrapper matching the paper label.
    prop:logic-expansion-forcing-persistence -/
theorem paper_logic_expansion_forcing_persistence
    {ContextSmall ContextLarge ValSmall ValLarge Formula : Type}
    (restrict : ValLarge → ValSmall) (lift : Formula → Formula)
    (satisfiesSmall : ValSmall → Formula → Prop) (satisfiesLarge : ValLarge → Formula → Prop)
    (p : InformationState ContextSmall ValSmall) (q : InformationState ContextLarge ValLarge)
    (href : ∀ {σ}, σ ∈ q.realizations → restrict σ ∈ p.realizations)
    (hlift : ∀ (σ : ValLarge) (φ : Formula),
      satisfiesSmall (restrict σ) φ → satisfiesLarge σ (lift φ))
    {φ : Formula} (hp : Forces satisfiesSmall p φ) :
    Forces satisfiesLarge q (lift φ) :=
  paper_logic_expansion_forcing_persistence_package
    restrict lift satisfiesSmall satisfiesLarge p q href hlift hp

end Omega.LogicExpansionChain.ForcingPersistence
