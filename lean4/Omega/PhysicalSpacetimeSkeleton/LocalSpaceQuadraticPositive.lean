import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton.LocalSpaceQuadraticPositive

open Matrix

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: an injective local-space map has strictly positive pulled-back quadratic form
    on every nonzero vector.
    prop:physical-spacetime-local-space-quadratic-positive -/
theorem paper_physical_spacetime_local_space_quadratic_positive_seeds
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Function.Injective A.mulVec)
    (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < dotProduct v ((A.transpose * A).mulVec v) := by
  have hAv_ne : A.mulVec v ≠ 0 := by
    intro hAv
    apply hv
    apply hA
    simpa using hAv
  have hquad :
      dotProduct v ((A.transpose * A).mulVec v) = dotProduct (A.mulVec v) (A.mulVec v) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rw [hquad]
  have hnonneg : 0 ≤ dotProduct (A.mulVec v) (A.mulVec v) := by
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((A.mulVec v) i)
  have hne : dotProduct (A.mulVec v) (A.mulVec v) ≠ 0 := by
    intro hzero
    exact hAv_ne (dotProduct_self_eq_zero.mp hzero)
  exact lt_of_le_of_ne hnonneg hne.symm

/-- Wrapper theorem matching the paper-facing package name.
    prop:physical-spacetime-local-space-quadratic-positive -/
theorem paper_physical_spacetime_local_space_quadratic_positive_package
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Function.Injective A.mulVec)
    (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < dotProduct v ((A.transpose * A).mulVec v) :=
  paper_physical_spacetime_local_space_quadratic_positive_seeds A hA v hv

/-- Paper-facing theorem using the canonical final name from the implementation ledger.
    prop:physical-spacetime-local-space-quadratic-positive -/
theorem paper_physical_spacetime_local_space_quadratic_positive
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : Function.Injective A.mulVec)
    (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < dotProduct v ((A.transpose * A).mulVec v) :=
  paper_physical_spacetime_local_space_quadratic_positive_seeds A hA v hv

end Omega.PhysicalSpacetimeSkeleton.LocalSpaceQuadraticPositive
