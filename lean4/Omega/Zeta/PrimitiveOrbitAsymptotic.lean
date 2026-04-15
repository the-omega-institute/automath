import Mathlib

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the primitive-orbit Perron asymptotic in the
    Fredholm--Witt preliminaries.
    lem:primitive-orbit-asymptotic -/
theorem paper_fredholm_witt_primitive_orbit_asymptotic
    (perronAsymptotic divisorTailBound primitiveOrbitAsymptotic : Prop)
    (hMain : perronAsymptotic)
    (hTail : divisorTailBound)
    (hAsymptotic : perronAsymptotic → divisorTailBound → primitiveOrbitAsymptotic) :
    primitiveOrbitAsymptotic := by
  exact hAsymptotic hMain hTail

end Omega.Zeta
