import Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

/-- Paper label: `prop:fold-jones-matrix-units`.
The canonical fiberwise matrix units are already packaged by the fold Jones direct-sum theorem. -/
theorem paper_fold_jones_matrix_units (fold : Ω → X) :
    matrixUnitGeneration fold := by
  exact (paper_op_algebra_fold_jones_basic_construction_directsum fold).2.1

end

end Omega.OperatorAlgebra
