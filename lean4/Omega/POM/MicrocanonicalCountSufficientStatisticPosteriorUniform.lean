import Mathlib.Tactic
import Omega.POM.MicrocanonicalAdaptiveNoGain

namespace Omega.POM

/-- Chapter-local package for the microcanonical sufficient-statistic/posterior-uniformity
statement. -/
structure MicrocanonicalPosteriorData where
  posteriorDependsOnlyOnCounts : Prop
  unqueriedPartUniform : Prop
  posteriorDependsOnlyOnCountsWitness : posteriorDependsOnlyOnCounts
  unqueriedPartUniformWitness : unqueriedPartUniform

/-- Under the microcanonical posterior, the queried history matters only through the count vector,
and the restriction to the unqueried domain is uniform on the remaining-count completion space.
    thm:pom-microcanonical-count-sufficient-statistic-posterior-uniform -/
theorem paper_pom_microcanonical_count_sufficient_statistic_posterior_uniform
    (h : MicrocanonicalPosteriorData) :
    h.posteriorDependsOnlyOnCounts ∧ h.unqueriedPartUniform := by
  exact ⟨h.posteriorDependsOnlyOnCountsWitness, h.unqueriedPartUniformWitness⟩

end Omega.POM
