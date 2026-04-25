import Omega.POM.MicrocanonicalCoverTimeNlognScale

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `thm:pom-microcanonical-cover-time-gumbel-cutoff`. -/
def paper_pom_microcanonical_cover_time_gumbel_cutoff : Prop := by
  exact
    ∀ {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (d : α → ℕ) {cLower cUpper : ℝ},
      microcanonicalBalancedCounts d cLower cUpper →
        microcanonicalNlognScaleSeparation d →
          (∀ (σ τ : Fin (microcanonicalTotalMass d) → α),
            microcanonicalStrategyCoverTimeMean d σ =
              microcanonicalStrategyCoverTimeMean d τ) ∧
            (∀ t : ℕ,
              microcanonicalCoverTimeTailFormula d t =
                Finset.sum ((Finset.univ : Finset α).powerset.filter Finset.Nonempty) fun A =>
                  (-1 : ℚ) ^ (A.card + 1) * microcanonicalSubsetAbsentProb d t A) ∧
            (microcanonicalCoverTimeMean d =
              Finset.sum (Finset.range (microcanonicalTotalMass d)) fun t =>
                Finset.sum ((Finset.univ : Finset α).powerset.filter Finset.Nonempty) fun A =>
                  (-1 : ℚ) ^ (A.card + 1) * microcanonicalSubsetAbsentProb d t A) ∧
            ∃ C1 C2 : ℝ,
              0 < C1 ∧
                0 < C2 ∧
                  microcanonicalNlognMeanWindow d C1 C2 ∧
                    microcanonicalCoverTimeOPnConcentration d

end Omega.POM
