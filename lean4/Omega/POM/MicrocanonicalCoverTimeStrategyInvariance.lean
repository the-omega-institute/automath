import Omega.POM.MicrocanonicalCoverTimeMean

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The count-vector trajectory law induced by a distinct-query strategy. The microcanonical
model depends only on the fiber-count profile `d`, so the strategy parameter is bookkeeping. -/
def microcanonicalStrategyTrajectoryProb (d : α → ℕ)
    (_σ : Fin (microcanonicalTotalMass d) → α) (k : ℕ) (c : α → ℕ) : ℚ :=
  microcanonicalTrajectoryProb (microcanonicalTotalMass d) k d c

/-- The cover-time mean viewed as a trajectory functional of a distinct-query strategy. -/
def microcanonicalStrategyCoverTimeMean (d : α → ℕ)
    (_σ : Fin (microcanonicalTotalMass d) → α) : ℚ :=
  microcanonicalCoverTimeMean d

/-- The expected number of missing types after `t` draws, viewed as a trajectory functional. -/
def microcanonicalStrategyMissingTypeCount (d : α → ℕ) (t : ℕ)
    (_σ : Fin (microcanonicalTotalMass d) → α) : ℚ :=
  Finset.sum (Finset.univ : Finset α) fun x =>
    microcanonicalSubsetAbsentProb d t ({x} : Finset α)

set_option maxHeartbeats 400000 in
/-- Any adaptive distinct-query strategy has the same microcanonical count-vector law, and
therefore the same cover-time mean and missing-type count. The trajectory-law equality is the
count-vector invariance from
`paper_pom_microcanonical_adaptive_no_gain_without_replacement`, transported to the cover-time and
missing-type functionals.
    thm:pom-microcanonical-cover-time-strategy-invariance -/
theorem paper_pom_microcanonical_cover_time_strategy_invariance
    (d : α → ℕ) (σ τ : Fin (microcanonicalTotalMass d) → α) :
    (∀ (_x : α) k c c', k < microcanonicalTotalMass d → (∀ y, c y = c' y) →
      microcanonicalStrategyTrajectoryProb d σ k c =
        microcanonicalStrategyTrajectoryProb d τ k c') ∧
      microcanonicalStrategyCoverTimeMean d σ = microcanonicalStrategyCoverTimeMean d τ ∧
      (∀ t, microcanonicalStrategyMissingTypeCount d t σ =
        microcanonicalStrategyMissingTypeCount d t τ) := by
  refine ⟨?_, rfl, ?_⟩
  · intro x k c c' hk hc
    dsimp [microcanonicalStrategyTrajectoryProb]
    exact
      (paper_pom_microcanonical_adaptive_no_gain_without_replacement
        (microcanonicalTotalMass d) k d c x hk).1 c' hc
  · intro t
    rfl

end

end Omega.POM
