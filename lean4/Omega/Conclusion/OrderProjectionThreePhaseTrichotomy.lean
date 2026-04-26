import Mathlib.Tactic
import Omega.Conclusion.FreeEnergyGatesMonotonicityObstruction
import Omega.POM.BooleanCircuitProjectionBudget
import Omega.POM.FirstfitExtensionalUndecidable
import Omega.POM.ValPolynomialSemantics

namespace Omega.Conclusion

open Omega.POM

/-- The three phase markers in the order-projection threshold wrapper. -/
inductive conclusion_order_projection_three_phase_trichotomy_phase
  | value
  | comparison
  | firstfit
  deriving DecidableEq

/-- The value layer contains only the polynomial semantics phase. -/
def conclusion_order_projection_three_phase_trichotomy_Wval :
    Set conclusion_order_projection_three_phase_trichotomy_phase :=
  {conclusion_order_projection_three_phase_trichotomy_phase.value}

/-- The comparison layer adds the comparison-order phase. -/
def conclusion_order_projection_three_phase_trichotomy_Wcmp :
    Set conclusion_order_projection_three_phase_trichotomy_phase :=
  {conclusion_order_projection_three_phase_trichotomy_phase.value,
    conclusion_order_projection_three_phase_trichotomy_phase.comparison}

/-- The first-fit layer adds the universal first-fit phase on top of the comparison layer. -/
def conclusion_order_projection_three_phase_trichotomy_Wff :
    Set conclusion_order_projection_three_phase_trichotomy_phase :=
  {conclusion_order_projection_three_phase_trichotomy_phase.value,
    conclusion_order_projection_three_phase_trichotomy_phase.comparison,
    conclusion_order_projection_three_phase_trichotomy_phase.firstfit}

/-- Concrete three-phase wrapper collecting value-language polynomial semantics, the monotonicity
obstruction, the one-gate NAND witness, the first-fit undecidability transfer, explicit strict
inclusion witnesses, and four concrete membership equivalences for the three phases. -/
def conclusion_order_projection_three_phase_trichotomy_statement : Prop :=
  (∀ {n k : ℕ} (w : ValWord n k), ValPolynomialSemantics w) ∧
    ((∀ n : ℕ, ∀ g : FreeEnergyGate n, CoordinatewiseMonotone g.eval) ∧
      (∀ n : ℕ, ∀ g : FreeEnergyGate n, ∀ f : (Fin n → Bool) → Bool,
        CompilesToBoolean g f → MonotoneBoolFunction f) ∧
      (∀ g : FreeEnergyGate 1, ¬ CompilesToBoolean g boolNotGate) ∧
      (∀ g : FreeEnergyGate 2, ¬ CompilesToBoolean g oddParityTwoGate)) ∧
    (booleanCircuitCompilesCorrectly ∧
      booleanCircuitNormProjCalls 1 = 1 ∧
      booleanCircuitOrderProjCalls 1 = 1 ∧
      nonmonotoneBooleanNeedsOrderProj) ∧
    (∀ {Hard Soft : Type*} (hardEq : Hard → Hard → Prop) (softEq : Soft → Soft → Prop)
      (compile : Hard → Soft),
        (∀ w1 w2, hardEq w1 w2 ↔ softEq (compile w1) (compile w2)) →
          (¬ Nonempty (∀ w1 w2, Decidable (hardEq w1 w2))) →
            ¬ Nonempty (∀ u v, Decidable (softEq u v))) ∧
    (conclusion_order_projection_three_phase_trichotomy_phase.comparison ∈
        conclusion_order_projection_three_phase_trichotomy_Wcmp ∧
      conclusion_order_projection_three_phase_trichotomy_phase.comparison ∉
        conclusion_order_projection_three_phase_trichotomy_Wval) ∧
    (conclusion_order_projection_three_phase_trichotomy_phase.firstfit ∈
        conclusion_order_projection_three_phase_trichotomy_Wff ∧
      conclusion_order_projection_three_phase_trichotomy_phase.firstfit ∉
        conclusion_order_projection_three_phase_trichotomy_Wcmp) ∧
    (∀ p,
      p ∈ conclusion_order_projection_three_phase_trichotomy_Wval ↔
        p = conclusion_order_projection_three_phase_trichotomy_phase.value) ∧
    (∀ p,
      p ∈ conclusion_order_projection_three_phase_trichotomy_Wcmp ↔
        p = conclusion_order_projection_three_phase_trichotomy_phase.value ∨
          p = conclusion_order_projection_three_phase_trichotomy_phase.comparison) ∧
    (∀ p,
      p ∈ conclusion_order_projection_three_phase_trichotomy_Wff ↔
        p = conclusion_order_projection_three_phase_trichotomy_phase.value ∨
          p = conclusion_order_projection_three_phase_trichotomy_phase.comparison ∨
          p = conclusion_order_projection_three_phase_trichotomy_phase.firstfit) ∧
    (∀ p,
      p ∈ conclusion_order_projection_three_phase_trichotomy_Wff ∧
        p ∉ conclusion_order_projection_three_phase_trichotomy_Wcmp ↔
          p = conclusion_order_projection_three_phase_trichotomy_phase.firstfit)

/-- Paper label: `thm:conclusion-order-projection-three-phase-trichotomy`. -/
theorem paper_conclusion_order_projection_three_phase_trichotomy :
    conclusion_order_projection_three_phase_trichotomy_statement := by
  refine ⟨?_, paper_conclusion_free_energy_gates_monotonicity_obstruction,
    paper_pom_boolean_circuit_projection_budget 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n k w
    exact paper_pom_val_polynomial_semantics w
  · intro Hard Soft hardEq softEq compile hCompile hUndecidable
    exact paper_pom_firstfit_extensional_undecidable hardEq softEq compile hCompile hUndecidable
  · constructor <;> simp [conclusion_order_projection_three_phase_trichotomy_Wcmp,
      conclusion_order_projection_three_phase_trichotomy_Wval]
  · constructor <;> simp [conclusion_order_projection_three_phase_trichotomy_Wff,
      conclusion_order_projection_three_phase_trichotomy_Wcmp]
  · intro p
    simp [conclusion_order_projection_three_phase_trichotomy_Wval]
  · intro p
    simp [conclusion_order_projection_three_phase_trichotomy_Wcmp]
  · intro p
    simp [conclusion_order_projection_three_phase_trichotomy_Wff]
  · intro p
    cases p <;> simp [conclusion_order_projection_three_phase_trichotomy_Wff,
      conclusion_order_projection_three_phase_trichotomy_Wcmp]

end Omega.Conclusion
