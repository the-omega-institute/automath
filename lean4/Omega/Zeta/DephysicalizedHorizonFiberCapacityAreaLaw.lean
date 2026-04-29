import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `prop:dephys-horizon-fiber-capacity-area-law`. -/
theorem paper_dephys_horizon_fiber_capacity_area_law
    (fiberLogCapacity blackHoleEntropy boundaryArea : ℝ)
    (hSaturates : fiberLogCapacity = blackHoleEntropy)
    (hAreaLaw : blackHoleEntropy = boundaryArea / 4) :
    fiberLogCapacity = boundaryArea / 4 := by
  rw [hSaturates, hAreaLaw]

end Omega.Zeta
