import Omega.OperatorAlgebra.FoldSqrtIndexFieldBasic
import Omega.OperatorAlgebra.FoldUnlinkEvaluatesToCollisionMoment

namespace Omega.OperatorAlgebra

open scoped BigOperators
open FoldJonesBasicConstructionDirectsum

theorem paper_op_algebra_fold_bm_valued_tl_jones {OmegaTy XTy : Type*} [Fintype OmegaTy]
    [DecidableEq OmegaTy] [Fintype XTy] [DecidableEq XTy] (fold : OmegaTy -> XTy) :
    directsumMatrixDecomposition fold ∧
      (∀ x, foldSqrtIndexField fold x ^ 2 = (Fintype.card (foldFiber fold x) : Real)) ∧
      (((∑ x, (foldWatataniIndexElement fold x : Rat) ^ 2) / Fintype.card OmegaTy) =
        foldWatataniTracedIndexMoment fold 1) := by
  have hJones := paper_op_algebra_fold_jones_basic_construction_directsum fold
  have hSqrt := paper_op_algebra_fold_sqrt_index_field_basic fold
  refine ⟨hJones.1, hSqrt.1, ?_⟩
  simp [foldWatataniTracedIndexMoment, foldWatataniIndexElement, foldWatataniIndexCoefficient]

end Omega.OperatorAlgebra
