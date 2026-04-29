import Omega.OperatorAlgebra.FoldWatataniIndexMoments

namespace Omega.OperatorAlgebra

/-- Paper label: `cor:op-algebra-fold-unlink-evaluates-to-collision-moment`. This is the traced
Watatani-index moment formula rewritten using the blockwise index element notation. -/
theorem paper_op_algebra_fold_unlink_evaluates_to_collision_moment {OmegaTy XTy : Type}
    [Fintype OmegaTy] [DecidableEq OmegaTy] [Fintype XTy] [DecidableEq XTy]
    (fold : OmegaTy -> XTy) (m r : Nat) (hcard : Fintype.card OmegaTy = 2 ^ m) :
    ((∑ x, (foldWatataniIndexElement fold x : Rat) ^ (r + 1)) / 2 ^ m) =
      foldWatataniTracedIndexMoment fold r := by
  simpa [foldWatataniIndexElement] using
    (paper_op_algebra_fold_watatani_index_moments fold m r hcard).2.2.symm

end Omega.OperatorAlgebra
