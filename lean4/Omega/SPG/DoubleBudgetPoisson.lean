namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Poisson threshold theorem for collision
    failure in the double-budget section.
    thm:double-budget-poisson -/
theorem paper_scan_projection_address_double_budget_poisson
    (syncNegligible collisionVanishing collisionCritical collisionExplosive
      thirdMomentVanishing varianceControlled thresholdScale : Prop)
    (subcriticalConclusion criticalConclusion supercriticalConclusion : Prop)
    (hSub :
      syncNegligible → collisionVanishing → subcriticalConclusion)
    (hCrit :
      syncNegligible →
        collisionCritical →
          thirdMomentVanishing → criticalConclusion)
    (hSuper :
      syncNegligible →
        collisionExplosive →
          varianceControlled → supercriticalConclusion)
    (hThreshold : thresholdScale) :
    (syncNegligible → collisionVanishing → subcriticalConclusion) ∧
      (syncNegligible →
        collisionCritical →
          thirdMomentVanishing → criticalConclusion) ∧
      (syncNegligible →
        collisionExplosive →
          varianceControlled → supercriticalConclusion) ∧
      thresholdScale := by
  exact ⟨hSub, hCrit, hSuper, hThreshold⟩

end Omega.SPG
