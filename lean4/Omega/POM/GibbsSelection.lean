import Omega.POM.PressureSlopes

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the discrete Gibbs-selection theorem in
    `2026_projection_ontological_mathematics_core_tams`.
    thm:gibbs-selection -/
theorem paper_projection_gibbs_selection
    (momentConvexity entropyRateConvexity perronRateConvexity renyiEndpoint
      pressureSlopeMonotone pressureSlopeLimit lowerTailEstimate upperTailEstimate
      bandConcentration : Prop)
    (hEntropy : momentConvexity → entropyRateConvexity)
    (hPerron : entropyRateConvexity → perronRateConvexity)
    (hEndpoint : perronRateConvexity → renyiEndpoint)
    (hSlopeMono : perronRateConvexity → pressureSlopeMonotone)
    (hSlopeLimit : renyiEndpoint → pressureSlopeLimit)
    (hLower : pressureSlopeMonotone → lowerTailEstimate)
    (hUpper : pressureSlopeMonotone → upperTailEstimate)
    (hBand : lowerTailEstimate → upperTailEstimate → bandConcentration) :
    momentConvexity →
      pressureSlopeMonotone ∧ lowerTailEstimate ∧ upperTailEstimate ∧ bandConcentration := by
  intro hMoment
  have hSlopes :=
    paper_projection_pressure_slopes
      momentConvexity entropyRateConvexity perronRateConvexity renyiEndpoint
      pressureSlopeMonotone pressureSlopeLimit hEntropy hPerron hEndpoint hSlopeMono hSlopeLimit
      hMoment
  have hMono : pressureSlopeMonotone := hSlopes.1
  have hLowerTail : lowerTailEstimate := hLower hMono
  have hUpperTail : upperTailEstimate := hUpper hMono
  exact ⟨hMono, hLowerTail, hUpperTail, hBand hLowerTail hUpperTail⟩

end Omega.POM
