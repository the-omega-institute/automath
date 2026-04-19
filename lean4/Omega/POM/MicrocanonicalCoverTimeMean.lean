import Mathlib.Tactic
import Omega.POM.MicrocanonicalCoverTimeTailInclusionExclusion

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The finite expected cover time written as the tail sum up to the total mass. -/
def microcanonicalCoverTimeMean (d : α → ℕ) : ℚ :=
  Finset.sum (Finset.range (microcanonicalTotalMass d)) fun t => microcanonicalCoverTimeTailFormula d t

omit [DecidableEq α] in
set_option maxHeartbeats 400000 in
/-- Paper-facing finite cover-time mean formula obtained by summing the inclusion-exclusion tail
law.
    cor:pom-microcanonical-cover-time-mean -/
theorem paper_pom_microcanonical_cover_time_mean (d : α → ℕ) :
    microcanonicalCoverTimeMean d =
      Finset.sum (Finset.range (microcanonicalTotalMass d)) fun t =>
        Finset.sum ((Finset.univ : Finset α).powerset.filter Finset.Nonempty) fun A =>
          (-1 : ℚ) ^ (A.card + 1) * microcanonicalSubsetAbsentProb d t A := by
  simp [microcanonicalCoverTimeMean, microcanonicalCoverTimeTailFormula]

end

end Omega.POM
