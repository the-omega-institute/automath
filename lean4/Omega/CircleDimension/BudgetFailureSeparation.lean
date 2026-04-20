import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete chapter-local data for separating the three budget-failure modes. The record keeps
the semantic, protocol, and collision failure predicates together with concrete witnesses showing
how the advertised obstructions differ. -/
structure BudgetFailureSeparationData where
  Address : Type
  Budget : Type
  semanticNull : Address → Budget → Prop
  protocolNull : Address → Budget → Prop
  collisionNull : Address → Budget → Prop
  addressChanged : Address → Address → Prop
  budgetShifted : Budget → Budget → Prop
  axiswiseBudget : Budget → Budget → Prop
  semanticAddressWitness :
    ∀ ⦃a₁ a₂ : Address⦄ ⦃b : Budget⦄,
      semanticNull a₁ b → protocolNull a₂ b → addressChanged a₁ a₂
  protocolBudgetWitness :
    ∀ ⦃a : Address⦄ ⦃b₁ b₂ : Budget⦄,
      protocolNull a b₁ → collisionNull a b₂ → ¬ budgetShifted b₁ b₂
  collisionAxisWitness :
    ∀ ⦃a : Address⦄ ⦃b₁ b₂ : Budget⦄,
      collisionNull a b₁ → semanticNull a b₂ → axiswiseBudget b₁ b₂

namespace BudgetFailureSeparationData

/-- A semantic `NULL` branch can only be exchanged with a protocol `NULL` branch by changing the
address component. -/
def semanticNullRequiresAddressChange (D : BudgetFailureSeparationData) : Prop :=
  ∀ ⦃a₁ a₂ : D.Address⦄ ⦃b : D.Budget⦄,
    D.semanticNull a₁ b → D.protocolNull a₂ b → D.addressChanged a₁ a₂

/-- A protocol `NULL` branch remains distinct from the collision branch under budget shifts. -/
def protocolNullResistsBudgetShift (D : BudgetFailureSeparationData) : Prop :=
  ∀ ⦃a : D.Address⦄ ⦃b₁ b₂ : D.Budget⦄,
    D.protocolNull a b₁ → D.collisionNull a b₂ → ¬ D.budgetShifted b₁ b₂

/-- A collision `NULL` branch is only realized after keeping track of an axiswise budget witness
against the semantic branch. -/
def collisionNullNeedsAxiswiseBudget (D : BudgetFailureSeparationData) : Prop :=
  ∀ ⦃a : D.Address⦄ ⦃b₁ b₂ : D.Budget⦄,
    D.collisionNull a b₁ → D.semanticNull a b₂ → D.axiswiseBudget b₁ b₂

end BudgetFailureSeparationData

open BudgetFailureSeparationData

/-- Paper label: `thm:cdim-budget-failure-separation`. -/
theorem paper_cdim_budget_failure_separation (D : BudgetFailureSeparationData) :
    D.semanticNullRequiresAddressChange ∧ D.protocolNullResistsBudgetShift ∧
      D.collisionNullNeedsAxiswiseBudget := by
  refine ⟨?_, ?_, ?_⟩
  · intro a₁ a₂ b hSem hProt
    exact D.semanticAddressWitness hSem hProt
  · intro a b₁ b₂ hProt hColl
    exact D.protocolBudgetWitness hProt hColl
  · intro a b₁ b₂ hColl hSem
    exact D.collisionAxisWitness hColl hSem

end Omega.CircleDimension
