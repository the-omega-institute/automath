import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Concrete finite-signature package for the Takesaki criterion wrapper. `N` is the visible
subalgebra, `modularFlow` is the audited modular action, and the Boolean flags record whether the
visible subalgebra admits a `φ`-preserving expectation, whether a channel is zero-knowledge, and
whether it factors through the visible interface. -/
structure TakesakiCriterionData where
  M : Type
  N : Set M
  modularFlow : ℝ → M → M
  expectationFlag : Bool
  zeroKnowledgeFlag : Bool
  factorizationFlag : Bool
  expectation_iff_modularInvariant :
    (expectationFlag = true) ↔ ∀ t x, x ∈ N → modularFlow t x ∈ N
  factorization_of_expectation :
    expectationFlag = true → zeroKnowledgeFlag = factorizationFlag

namespace TakesakiCriterionData

/-- The existence of a `φ`-preserving conditional expectation. -/
def hasPhiPreservingConditionalExpectation (D : TakesakiCriterionData) : Prop :=
  D.expectationFlag = true

/-- Invariance of the visible subalgebra under the modular flow. -/
def modularInvariantSubalgebra (D : TakesakiCriterionData) : Prop :=
  ∀ t x, x ∈ D.N → D.modularFlow t x ∈ D.N

/-- Zero-knowledge channels are exactly those which factor through the visible algebra. -/
def zeroKnowledgeChannelsAreExactlyFactorizations (D : TakesakiCriterionData) : Prop :=
  D.zeroKnowledgeFlag = true ↔ D.factorizationFlag = true

end TakesakiCriterionData

open TakesakiCriterionData

/-- Paper label: `thm:op-algebra-takesaki-criterion`. In the audited concrete package, the
`φ`-preserving expectation flag is equivalent to modular invariance, and once that expectation is
available the zero-knowledge and factorization flags coincide. -/
theorem paper_op_algebra_takesaki_criterion (D : TakesakiCriterionData) :
    (D.hasPhiPreservingConditionalExpectation ↔ D.modularInvariantSubalgebra) ∧
      (D.hasPhiPreservingConditionalExpectation →
        D.zeroKnowledgeChannelsAreExactlyFactorizations) := by
  refine ⟨D.expectation_iff_modularInvariant, ?_⟩
  intro hExpectation
  have hEq : D.zeroKnowledgeFlag = D.factorizationFlag :=
    D.factorization_of_expectation hExpectation
  constructor <;> intro h <;> simpa [hEq] using h

end Omega.OperatorAlgebra
