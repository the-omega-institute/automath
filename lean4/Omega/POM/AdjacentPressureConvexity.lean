import Omega.POM.GlobalPressureConvexityPublication

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the adjacent pressure-convexity corollary in
    `2026_projection_ontological_mathematics_core_tams`.
    cor:cross-q-logconvex -/
theorem paper_projection_adjacent_pressure_convexity
    (momentConvexity entropyRateConvexity perronRateConvexity adjacentPressureConvexity : Prop)
    (hEntropy : momentConvexity → entropyRateConvexity)
    (hPerron : entropyRateConvexity → perronRateConvexity)
    (hAdjacent : perronRateConvexity → adjacentPressureConvexity) :
    momentConvexity →
      momentConvexity ∧
        entropyRateConvexity ∧
        perronRateConvexity ∧ adjacentPressureConvexity := by
  intro hMoment
  have hGlobal :=
    paper_projection_global_pressure_convexity
      momentConvexity entropyRateConvexity perronRateConvexity hEntropy hPerron hMoment
  exact ⟨hGlobal.1, hGlobal.2.1, hGlobal.2.2, hAdjacent hGlobal.2.2⟩

end Omega.POM
