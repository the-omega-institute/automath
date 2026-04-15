import Omega.SPG.DoubleBudgetPoisson

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the subcritical capacity region corollary.
    cor:capacity-region -/
theorem paper_scan_projection_address_capacity_region
    (syncNegligible collisionVanishing collisionCritical collisionExplosive
      thirdMomentVanishing varianceControlled thresholdScale : Prop)
    (failProbZero criticalConclusion supercriticalConclusion : Prop)
    (hSync : syncNegligible)
    (hCollision : collisionVanishing)
    (hSub :
      syncNegligible → collisionVanishing → failProbZero)
    (hCrit :
      syncNegligible →
        collisionCritical →
          thirdMomentVanishing → criticalConclusion)
    (hSuper :
      syncNegligible →
        collisionExplosive →
          varianceControlled → supercriticalConclusion)
    (hThreshold : thresholdScale) :
    failProbZero := by
  have hPoisson :=
    paper_scan_projection_address_double_budget_poisson
      syncNegligible collisionVanishing collisionCritical collisionExplosive
      thirdMomentVanishing varianceControlled thresholdScale
      failProbZero criticalConclusion supercriticalConclusion
      hSub hCrit hSuper hThreshold
  exact hPoisson.1 hSync hCollision

end Omega.SPG
