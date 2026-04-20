import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum

open scoped BigOperators

namespace Omega.OperatorAlgebra

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

open FoldJonesBasicConstructionDirectsum

/-- The Watatani index coefficient on the `x`-block is the fiber cardinality `d_x`. -/
def foldCenterExpectationIndexField (fold : Ω → X) (x : X) : ℕ :=
  Fintype.card (foldFiber fold x)

/-- The canonical trace of the Watatani index field in the block-diagonal model. -/
def foldCenterExpectationTraceOfIndex (fold : Ω → X) : ℚ :=
  (∑ x, (foldCenterExpectationIndexField fold x : ℚ) *
      (Fintype.card (foldFiber fold x) : ℚ)) / Fintype.card Ω

/-- The second collision moment `S₂ = ∑ₓ dₓ²`. -/
def foldCenterExpectationSecondCollisionMoment (fold : Ω → X) : ℚ :=
  ∑ x, (Fintype.card (foldFiber fold x) : ℚ) ^ 2

/-- In the Jones basic-construction direct-sum decomposition, the blockwise normalized-trace
expectation has Watatani index field `d_x`, and its canonical trace evaluates to the normalized
second collision moment.
    thm:op-algebra-fold-center-expectation-index-collision2 -/
theorem paper_op_algebra_fold_center_expectation_index_collision2
    (fold : Ω → X) (m : ℕ) (hcard : Fintype.card Ω = 2 ^ m) :
    directsumMatrixDecomposition fold ∧
      (∀ x, foldCenterExpectationIndexField fold x = Fintype.card (foldFiber fold x)) ∧
      foldCenterExpectationTraceOfIndex fold =
        foldCenterExpectationSecondCollisionMoment fold / 2 ^ m := by
  have hJones := paper_op_algebra_fold_jones_basic_construction_directsum fold
  refine ⟨hJones.1, ?_, ?_⟩
  · intro x
    rfl
  · unfold foldCenterExpectationTraceOfIndex foldCenterExpectationSecondCollisionMoment
      foldCenterExpectationIndexField
    simp [hcard, pow_two]

end

end Omega.OperatorAlgebra
