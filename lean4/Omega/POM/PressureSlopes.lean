import Omega.POM.GlobalPressureConvexityPublication

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the pressure-slopes corollary in
    `2026_projection_ontological_mathematics_core_tams`.
    cor:pressure-slopes -/
theorem paper_projection_pressure_slopes
    (momentConvexity entropyRateConvexity perronRateConvexity renyiEndpoint
      pressureSlopeMonotone pressureSlopeLimit : Prop)
    (hEntropy : momentConvexity → entropyRateConvexity)
    (hPerron : entropyRateConvexity → perronRateConvexity)
    (hEndpoint : perronRateConvexity → renyiEndpoint)
    (hSlopeMono : perronRateConvexity → pressureSlopeMonotone)
    (hSlopeLimit : renyiEndpoint → pressureSlopeLimit) :
    momentConvexity → pressureSlopeMonotone ∧ pressureSlopeLimit := by
  intro hMoment
  have hGlobal :=
    paper_projection_global_pressure_convexity
      momentConvexity entropyRateConvexity perronRateConvexity hEntropy hPerron hMoment
  have hPerronRate : perronRateConvexity := hGlobal.2.2
  have hEndpoint' : renyiEndpoint := hEndpoint hPerronRate
  exact ⟨hSlopeMono hPerronRate, hSlopeLimit hEndpoint'⟩

end Omega.POM
