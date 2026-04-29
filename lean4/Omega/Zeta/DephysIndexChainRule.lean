import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The composite conditional expectation `E20 = E10 ∘ E21`. -/
def cor_dephys_index_chain_rule_composite_expectation {State : Type*}
    (E10 E21 : State → State) : State → State :=
  fun x => E10 (E21 x)

/-- Finite-index multiplicativity for the nested expectations. -/
def cor_dephys_index_chain_rule_composite_index (ind10 ind21 : ℝ) : ℝ :=
  ind21 * ind10

/-- The relative-entropy defect associated to a conditional expectation. -/
def cor_dephys_index_chain_rule_relative_entropy_defect {State : Type*}
    (D : State → State → ℝ) (E : State → State) (ρ σ : State) : ℝ :=
  D ρ σ - D (E ρ) (E σ)

/-- Concrete proposition collecting multiplicativity of the finite index and the telescoping
chain rule for the relative-entropy defect under `E20 = E10 ∘ E21`. -/
def cor_dephys_index_chain_rule_statement : Prop :=
  (∀ ind10 ind21 : ℝ, 0 < ind10 → 0 < ind21 →
      cor_dephys_index_chain_rule_composite_index ind10 ind21 = ind21 * ind10 ∧
        Real.log (cor_dephys_index_chain_rule_composite_index ind10 ind21) =
          Real.log ind21 + Real.log ind10) ∧
    (∀ {State : Type} (D : State → State → ℝ) (E10 E21 : State → State) (ρ σ : State),
      cor_dephys_index_chain_rule_relative_entropy_defect D
          (cor_dephys_index_chain_rule_composite_expectation E10 E21) ρ σ =
        cor_dephys_index_chain_rule_relative_entropy_defect D E21 ρ σ +
          cor_dephys_index_chain_rule_relative_entropy_defect D E10 (E21 ρ) (E21 σ))

theorem cor_dephys_index_chain_rule_verified : cor_dephys_index_chain_rule_statement := by
  refine ⟨?_, ?_⟩
  · intro ind10 ind21 hind10 hind21
    refine ⟨rfl, ?_⟩
    rw [cor_dephys_index_chain_rule_composite_index,
      Real.log_mul (ne_of_gt hind21) (ne_of_gt hind10)]
  · intro State D E10 E21 ρ σ
    unfold cor_dephys_index_chain_rule_relative_entropy_defect
      cor_dephys_index_chain_rule_composite_expectation
    ring

/-- Paper label: `cor:dephys-index-chain-rule`. -/
def paper_dephys_index_chain_rule : Prop := by
  exact cor_dephys_index_chain_rule_statement

end Omega.Zeta
