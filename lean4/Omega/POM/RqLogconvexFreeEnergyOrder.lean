import Omega.POM.PressureSlopes

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper that packages the Rényi log-convexity/free-energy order chain together
    with the strictness clause.
    prop:pom-rq-logconvex-free-energy-order -/
theorem paper_pom_rq_logconvex_free_energy_order
    (momentConvexity perronRateConvexity pressureSlopeMonotone strictness : Prop)
    (hPerron : momentConvexity → perronRateConvexity)
    (hSlope : perronRateConvexity → pressureSlopeMonotone)
    (hStrict : momentConvexity → strictness) :
    momentConvexity → perronRateConvexity ∧ pressureSlopeMonotone ∧ strictness := by
  intro hMoment
  have hPerronRate : perronRateConvexity := hPerron hMoment
  exact ⟨hPerronRate, hSlope hPerronRate, hStrict hMoment⟩

end Omega.POM
