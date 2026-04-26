import Omega.POM.MicrocanonicalCountSufficientStatisticPosteriorUniform

namespace Omega.POM

/-- Paper label: `prop:pom-microcanonical-query-distortion-strategy-invariant-posterior`. -/
theorem paper_pom_microcanonical_query_distortion_strategy_invariant_posterior
    (h : MicrocanonicalPosteriorData) :
    h.unqueriedPartUniform ∧ h.posteriorDependsOnlyOnCounts := by
  exact ⟨h.unqueriedPartUniformWitness, h.posteriorDependsOnlyOnCountsWitness⟩

end Omega.POM
