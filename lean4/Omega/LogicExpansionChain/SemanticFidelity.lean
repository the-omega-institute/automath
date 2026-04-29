import Mathlib.Tactic

namespace Omega.LogicExpansionChain.SemanticFidelity

/-- Semantic entailment expressed directly through forcing. -/
def Entails {State Formula : Type} (forces : State → Formula → Prop)
    (Γ : Set Formula) (φ : Formula) : Prop :=
  ∀ p, (∀ ψ ∈ Γ, forces p ψ) → forces p φ

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: a realization map preserves semantic entailment.
    prop:logic-expansion-semantic-fidelity -/
theorem paper_logic_expansion_semantic_fidelity_seeds
    {AbstractState ConcreteState AbstractFormula ConcreteFormula : Type}
    (recover : ConcreteState → AbstractState) (interp : AbstractFormula → ConcreteFormula)
    (forcesAbstract : AbstractState → AbstractFormula → Prop)
    (forcesConcrete : ConcreteState → ConcreteFormula → Prop)
    (hreal : ∀ q ψ, forcesConcrete q (interp ψ) ↔ forcesAbstract (recover q) ψ)
    (Γ : Set AbstractFormula) (φ : AbstractFormula)
    (hΓ : Entails forcesAbstract Γ φ) :
    Entails forcesConcrete (interp '' Γ) (interp φ) := by
  intro q hq
  have hΓ' : ∀ ψ ∈ Γ, forcesAbstract (recover q) ψ := by
    intro ψ hψ
    exact (hreal q ψ).mp (hq (interp ψ) ⟨ψ, hψ, rfl⟩)
  exact (hreal q φ).mpr (hΓ (recover q) hΓ')

/-- Wrapper theorem matching the paper-facing package name.
    prop:logic-expansion-semantic-fidelity -/
theorem paper_logic_expansion_semantic_fidelity_package
    {AbstractState ConcreteState AbstractFormula ConcreteFormula : Type}
    (recover : ConcreteState → AbstractState) (interp : AbstractFormula → ConcreteFormula)
    (forcesAbstract : AbstractState → AbstractFormula → Prop)
    (forcesConcrete : ConcreteState → ConcreteFormula → Prop)
    (hreal : ∀ q ψ, forcesConcrete q (interp ψ) ↔ forcesAbstract (recover q) ψ)
    (Γ : Set AbstractFormula) (φ : AbstractFormula)
    (hΓ : Entails forcesAbstract Γ φ) :
    Entails forcesConcrete (interp '' Γ) (interp φ) :=
  paper_logic_expansion_semantic_fidelity_seeds
    recover interp forcesAbstract forcesConcrete hreal Γ φ hΓ

set_option maxHeartbeats 400000 in
/-- Exact paper-facing wrapper for the semantic-fidelity package.
    prop:logic-expansion-semantic-fidelity -/
theorem paper_logic_expansion_semantic_fidelity
    {AbstractState ConcreteState AbstractFormula ConcreteFormula : Type}
    (recover : ConcreteState → AbstractState) (interp : AbstractFormula → ConcreteFormula)
    (forcesAbstract : AbstractState → AbstractFormula → Prop)
    (forcesConcrete : ConcreteState → ConcreteFormula → Prop)
    (hreal : ∀ q ψ, forcesConcrete q (interp ψ) ↔ forcesAbstract (recover q) ψ)
    (Γ : Set AbstractFormula) (φ : AbstractFormula)
    (hΓ : Entails forcesAbstract Γ φ) :
    Entails forcesConcrete (interp '' Γ) (interp φ) :=
  paper_logic_expansion_semantic_fidelity_package
    recover interp forcesAbstract forcesConcrete hreal Γ φ hΓ

end Omega.LogicExpansionChain.SemanticFidelity
