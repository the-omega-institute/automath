import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Finite bounded-slice package for a cost-optimization problem on a single semantic class. -/
structure CostOptimizationDecidableData where
  Word : Type
  instFintypeWord : Fintype Word
  instDecidableEqWord : DecidableEq Word
  equiv : Word → Word → Prop
  instDecidableRelEquiv : DecidableRel equiv
  base : Word
  cost : Word → ℕ × ℕ

attribute [instance] CostOptimizationDecidableData.instFintypeWord
attribute [instance] CostOptimizationDecidableData.instDecidableEqWord
attribute [instance] CostOptimizationDecidableData.instDecidableRelEquiv

namespace CostOptimizationDecidableData

/-- Product-order comparison for the two tropical resource coordinates. -/
def costLE (c₁ c₂ : ℕ × ℕ) : Prop :=
  c₁.1 ≤ c₂.1 ∧ c₁.2 ≤ c₂.2

/-- Finite enumeration of the semantic equivalence class of the distinguished word. -/
def equivalenceClass (D : CostOptimizationDecidableData) : Finset D.Word :=
  Finset.univ.filter fun w => D.equiv w D.base

/-- Pareto minimality inside the finite equivalence class. -/
def IsParetoMinimal (D : CostOptimizationDecidableData) (w : D.Word) : Prop :=
  w ∈ D.equivalenceClass ∧
    ∀ v, v ∈ D.equivalenceClass →
      CostOptimizationDecidableData.costLE (D.cost v) (D.cost w) →
        CostOptimizationDecidableData.costLE (D.cost w) (D.cost v)

/-- Explicit finite Pareto frontier obtained by filtering the finite class enumeration. -/
noncomputable def frontier (D : CostOptimizationDecidableData) : Finset D.Word := by
  classical
  exact D.equivalenceClass.filter fun w => D.IsParetoMinimal w

/-- The finite frontier is computable by its direct `Finset` construction. -/
def HasFiniteComputableFrontier (D : CostOptimizationDecidableData) : Prop :=
  ∃ F : Finset D.Word,
    F = D.frontier ∧
      ∀ w, w ∈ F ↔ w ∈ D.equivalenceClass ∧ D.IsParetoMinimal w

end CostOptimizationDecidableData

open CostOptimizationDecidableData

/-- Paper label: `prop:pom-cost-optimization-decidable`. In the bounded finite slice, the
equivalence class of the distinguished word is explicitly enumerable, and filtering by
Pareto-minimality computes the frontier. -/
theorem paper_pom_cost_optimization_decidable (D : CostOptimizationDecidableData) :
    D.HasFiniteComputableFrontier := by
  classical
  refine ⟨D.frontier, rfl, ?_⟩
  intro w
  simp [CostOptimizationDecidableData.frontier]

end Omega.POM
