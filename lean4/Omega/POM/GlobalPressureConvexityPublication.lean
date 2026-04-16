namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the global pressure-convexity theorem in
    `2026_projection_ontological_mathematics_core_tams`.
    thm:global-pressure-convexity -/
theorem paper_projection_global_pressure_convexity
    (momentConvexity entropyRateConvexity perronRateConvexity : Prop)
    (hEntropy : momentConvexity → entropyRateConvexity)
    (hPerron : entropyRateConvexity → perronRateConvexity) :
    momentConvexity →
      momentConvexity ∧ entropyRateConvexity ∧ perronRateConvexity := by
  intro hMoment
  have hEntropyRate : entropyRateConvexity := hEntropy hMoment
  exact ⟨hMoment, hEntropyRate, hPerron hEntropyRate⟩

end Omega.POM
