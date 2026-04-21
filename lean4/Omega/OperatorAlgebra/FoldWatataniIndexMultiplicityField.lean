import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {OmegaTy XTy : Type*} [Fintype OmegaTy] [DecidableEq OmegaTy]
  [Fintype XTy] [DecidableEq XTy]

/-- Fiberwise size of the canonical quasi-basis vector attached to `ω`. In the finite diagonal
model this is the multiplicity of the `fold ω` block. -/
def foldWatataniFiberQuasiBasisWeight (fold : OmegaTy → XTy) (ω : OmegaTy) : ℕ :=
  Fintype.card (foldFiber fold (fold ω))

/-- The coefficient of the Watatani index element on the `x`-block. -/
def foldWatataniIndexCoefficient (fold : OmegaTy → XTy) (x : XTy) : ℕ :=
  Fintype.card (foldFiber fold x)

/-- Under the identification `B ≃ ℂ^X`, the Watatani index element is the multiplicity field
`x ↦ d_x`. -/
def foldWatataniIndexElement (fold : OmegaTy → XTy) : XTy → ℕ :=
  foldWatataniIndexCoefficient fold

/-- Concrete wrapper for the direct-sum Jones model and the closed form
`Ind_W(E) = Σ_x d_x P̃_x`, encoded as the statement that the blockwise index element is exactly
the multiplicity field. -/
def foldWatataniIndexMultiplicityField (fold : OmegaTy → XTy) : Prop :=
  directsumMatrixDecomposition fold ∧
    (∀ ω, foldWatataniFiberQuasiBasisWeight fold ω = Fintype.card (foldFiber fold (fold ω))) ∧
    ∀ x, foldWatataniIndexElement fold x = Fintype.card (foldFiber fold x)

/-- Paper label: `thm:op-algebra-fold-watatani-index-equals-multiplicity-field`.
In the finite direct-sum block model, the Watatani quasi-basis weights and the index element are
exactly the fiber multiplicities. -/
theorem paper_op_algebra_fold_watatani_index_equals_multiplicity_field
    (fold : OmegaTy → XTy) : foldWatataniIndexMultiplicityField fold := by
  refine ⟨(paper_op_algebra_fold_jones_basic_construction_directsum fold).1, ?_, ?_⟩
  · intro ω
    rfl
  · intro x
    rfl

end

end Omega.OperatorAlgebra
