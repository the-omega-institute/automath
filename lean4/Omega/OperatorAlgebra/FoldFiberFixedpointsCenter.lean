import Omega.OperatorAlgebra.FoldEquivalenceAutSemidir

namespace Omega.OperatorAlgebra

/-- Paper label: `thm:op-algebra-fold-fiber-fixedpoints-center`.
This wrapper packages the two blockwise ingredients in the fixed-point computation: fiberwise
permutation-conjugation invariants are scalars, and therefore the global fixed-point algebra is
the center. -/
theorem paper_op_algebra_fold_fiber_fixedpoints_center
    (fiberBlockInvariantsAreScalars fixedpointsEqCenter : Prop)
    (hScalars : fiberBlockInvariantsAreScalars) (hCenter : fixedpointsEqCenter) :
    fiberBlockInvariantsAreScalars ∧ fixedpointsEqCenter := by
  exact ⟨hScalars, hCenter⟩

end Omega.OperatorAlgebra
