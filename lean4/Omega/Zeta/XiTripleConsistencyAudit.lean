import Omega.LogicExpansionChain.ConcreteSemanticFidelity
import Omega.Zeta.HankelDeterminantalRadicalEqRigidity
import Omega.Zeta.LocalizedIntegersPadicKernelRigidity

namespace Omega.Zeta

/-- Auditable conjunction of the three consistency layers used in the paper-facing xi audit:
the localized-integers `p`-adic kernel guardrail, the finite Hankel rigidity package, and the
conservative semantic-fidelity transfer principle. -/
def paper_xi_triple_consistency_audit_statement : Prop :=
  (∀ h : LocalizedIntegersPadicKernelRigidityData,
    h.shortExactSequence ∧ h.connectedComponentIsCircle ∧ h.circleDimensionOne ∧
      h.padicKernelRecoversPrimeSet) ∧
    ((∀ ω₁ ω₂ ω₃ a₁ a₂ a₃ : ℤ,
      (hankel3 ω₁ ω₂ ω₃ a₁ a₂ a₃).det =
        ω₁ * ω₂ * ω₃ * (a₂ - a₁) ^ 2 * (a₃ - a₁) ^ 2 * (a₃ - a₂) ^ 2) ∧
      (∀ ω₁ ω₂ ω₃ a₁ a₂ a₃ : ℤ,
        (hankel3 ω₁ ω₂ ω₃ a₁ a₂ a₃).det = 0 ↔
          ω₁ = 0 ∨ ω₂ = 0 ∨ ω₃ = 0 ∨ a₁ = a₂ ∨ a₁ = a₃ ∨ a₂ = a₃)) ∧
    (∀ {AbstractState ConcreteState AbstractFormula ConcreteFormula : Type}
      (recover : ConcreteState → AbstractState)
      (interp : AbstractFormula → ConcreteFormula)
      (forcesAbstract : AbstractState → AbstractFormula → Prop)
      (forcesConcrete : ConcreteState → ConcreteFormula → Prop)
      (_hreal : ∀ q ψ, forcesConcrete q (interp ψ) ↔ forcesAbstract (recover q) ψ)
      (Γ : Set AbstractFormula) (φ : AbstractFormula),
      Omega.LogicExpansionChain.SemanticFidelity.Entails forcesAbstract Γ φ →
        Omega.LogicExpansionChain.SemanticFidelity.Entails
          forcesConcrete (interp '' Γ) (interp φ))

theorem paper_xi_triple_consistency_audit : paper_xi_triple_consistency_audit_statement := by
  refine ⟨?_, paper_xi_hankel_determinantal_radical_eq_rigidity, ?_⟩
  · intro h
    exact paper_xi_localized_integers_padic_kernel_rigidity h
  · intro AbstractState ConcreteState AbstractFormula ConcreteFormula recover interp
      forcesAbstract forcesConcrete hreal Γ φ hΓ
    exact Omega.LogicExpansionChain.paper_conservative_extension_semantic_fidelity_package
      recover interp forcesAbstract forcesConcrete hreal Γ φ hΓ

end Omega.Zeta
