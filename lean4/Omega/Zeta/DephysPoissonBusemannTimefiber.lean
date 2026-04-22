import Omega.UnitCirclePhaseArithmetic.AppBusemannPoissonMinusOne

namespace Omega.Zeta

/-- Dephysicalized corollary of the endpoint `-1` Poisson/Busemann identity.
    cor:dephys-poisson-busemann-timefiber -/
theorem paper_dephys_poisson_busemann_timefiber (x y : ℝ) (hy : 0 < y) :
    let t : Complex := (x : Complex) + y * Complex.I
    let w : Complex := (1 + Complex.I * t) / (1 - Complex.I * t)
    (1 - ‖w‖ ^ 2) / ‖1 + w‖ ^ 2 = y := by
  simpa using Omega.UnitCirclePhaseArithmetic.paper_app_busemann_poisson_minus1 x y hy

end Omega.Zeta
