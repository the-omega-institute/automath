import Mathlib.Data.Complex.Basic

namespace Omega.GroupUnification

/-- The twisted boundary map on the one-cell model of the circle is multiplication by
`1 - loopWeight`. -/
def groupJGTwistedBoundaryMap (loopWeight : ℂ) : ℂ :=
  1 - loopWeight

/-- In the one-dimensional local-system model, the determinant of the boundary operator is the same
scalar as the boundary map itself. -/
def groupJGEulerFactorBoundaryDet (loopWeight : ℂ) : ℂ :=
  groupJGTwistedBoundaryMap loopWeight

/-- The `GL₁` Euler factor is the determinant of the twisted boundary map on the one-cell circle.
    thm:group-jg-euler-factor-determinant-local-system -/
theorem paper_group_jg_euler_factor_determinant_local_system (loopWeight : ℂ) :
    groupJGEulerFactorBoundaryDet loopWeight = 1 - loopWeight := by
  rfl

end Omega.GroupUnification
