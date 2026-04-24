import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication wrapper for the four second-order Poisson--Cauchy profile-convergence outputs.
    prop:cdim-poisson-second-order-profile-convergence -/
theorem paper_cdim_poisson_second_order_profile_convergence
    (uniformDensityProfileConvergence densityLpProfileConvergence
      uniformRatioProfileConvergence weightedRatioLpConvergence : Prop)
    (hDensity : uniformDensityProfileConvergence)
    (hDensityLp : densityLpProfileConvergence)
    (hRatio : uniformRatioProfileConvergence)
    (hRatioLp : weightedRatioLpConvergence) :
    uniformDensityProfileConvergence ∧ densityLpProfileConvergence ∧
      uniformRatioProfileConvergence ∧ weightedRatioLpConvergence := by
  exact ⟨hDensity, hDensityLp, hRatio, hRatioLp⟩

end Omega.CircleDimension
