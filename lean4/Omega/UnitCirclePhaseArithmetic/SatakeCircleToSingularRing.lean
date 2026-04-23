import Mathlib

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:satake-circle-to-singular-ring`. -/
theorem paper_satake_circle_to_singular_ring
    (inverseSquareIdentity unitCircleImage ellipticImageDegeneration satakeCircleToSingularRing :
      Prop)
    (hInv : inverseSquareIdentity)
    (hUnit : unitCircleImage)
    (hEllipse : ellipticImageDegeneration)
    (hImpl : inverseSquareIdentity → unitCircleImage → ellipticImageDegeneration →
      satakeCircleToSingularRing) :
    satakeCircleToSingularRing := by
  exact hImpl hInv hUnit hEllipse

end Omega.UnitCirclePhaseArithmetic
