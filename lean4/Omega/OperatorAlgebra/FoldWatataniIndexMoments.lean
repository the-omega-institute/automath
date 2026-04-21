import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldCenterExpectationIndexCollision2
import Omega.OperatorAlgebra.FoldWatataniIndexMultiplicityField

namespace Omega.OperatorAlgebra

open scoped BigOperators
open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

/-- The normalized trace of the `q`-th power of the Watatani index field, written blockwise. -/
def foldWatataniTracedIndexMoment (fold : Ω → X) (q : ℕ) : ℚ :=
  (∑ x, (foldWatataniIndexCoefficient fold x : ℚ) ^ (q + 1)) / Fintype.card Ω

/-- Closed form for the traced Watatani index moments in the finite fold model. -/
def FoldWatataniIndexMomentsFormula (fold : Ω → X) (m q : ℕ) : Prop :=
  directsumMatrixDecomposition fold ∧
    (∀ x, foldWatataniIndexCoefficient fold x = Fintype.card (foldFiber fold x)) ∧
    foldWatataniTracedIndexMoment fold q =
      (∑ x, (Fintype.card (foldFiber fold x) : ℚ) ^ (q + 1)) / 2 ^ m

/-- Paper label: `cor:op-algebra-fold-watatani-index-moments`. -/
theorem paper_op_algebra_fold_watatani_index_moments {Ω X : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype X] [DecidableEq X] (fold : Ω → X) (m q : ℕ) (hcard : Fintype.card Ω = 2 ^ m) :
    FoldWatataniIndexMomentsFormula fold m q := by
  have hmult := paper_op_algebra_fold_watatani_index_equals_multiplicity_field fold
  refine ⟨hmult.1, ?_, ?_⟩
  · intro x
    rfl
  · unfold foldWatataniTracedIndexMoment foldWatataniIndexCoefficient
    simp [hcard]

end

end Omega.OperatorAlgebra
