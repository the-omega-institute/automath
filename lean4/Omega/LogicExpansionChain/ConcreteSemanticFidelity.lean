import Omega.LogicExpansionChain.SemanticFidelity

namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: any concrete realization preserving forcing carries abstract entailments to
    concrete entailments.
    prop:semantic-fidelity -/
theorem paper_conservative_extension_semantic_fidelity_seeds
    {AbstractState ConcreteState AbstractFormula ConcreteFormula : Type}
    (recover : ConcreteState → AbstractState) (interp : AbstractFormula → ConcreteFormula)
    (forcesAbstract : AbstractState → AbstractFormula → Prop)
    (forcesConcrete : ConcreteState → ConcreteFormula → Prop)
    (hreal : ∀ q ψ, forcesConcrete q (interp ψ) ↔ forcesAbstract (recover q) ψ)
    (Γ : Set AbstractFormula) (φ : AbstractFormula)
    (hΓ : SemanticFidelity.Entails forcesAbstract Γ φ) :
    SemanticFidelity.Entails forcesConcrete (interp '' Γ) (interp φ) :=
  SemanticFidelity.paper_logic_expansion_semantic_fidelity_seeds
    recover interp forcesAbstract forcesConcrete hreal Γ φ hΓ

/-- Packaged form of the concrete semantic-fidelity seed.
    prop:semantic-fidelity -/
theorem paper_conservative_extension_semantic_fidelity_package
    {AbstractState ConcreteState AbstractFormula ConcreteFormula : Type}
    (recover : ConcreteState → AbstractState) (interp : AbstractFormula → ConcreteFormula)
    (forcesAbstract : AbstractState → AbstractFormula → Prop)
    (forcesConcrete : ConcreteState → ConcreteFormula → Prop)
    (hreal : ∀ q ψ, forcesConcrete q (interp ψ) ↔ forcesAbstract (recover q) ψ)
    (Γ : Set AbstractFormula) (φ : AbstractFormula)
    (hΓ : SemanticFidelity.Entails forcesAbstract Γ φ) :
    SemanticFidelity.Entails forcesConcrete (interp '' Γ) (interp φ) :=
  paper_conservative_extension_semantic_fidelity_seeds
    recover interp forcesAbstract forcesConcrete hreal Γ φ hΓ

end Omega.LogicExpansionChain
