import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.POM.MicrocanonicalCoverTimeStrategyInvariance

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The number of visible types in the finite microcanonical model. -/
def microcanonicalTypeCount (_α : Type*) [Fintype _α] : ℕ :=
  Fintype.card _α

/-- Real-valued version of the visible-type count. -/
def microcanonicalTypeCountReal (_α : Type*) [Fintype _α] : ℝ :=
  (microcanonicalTypeCount _α : ℝ)

/-- Real-valued cover-time mean. -/
def microcanonicalCoverTimeMeanReal (d : α → ℕ) : ℝ :=
  (microcanonicalCoverTimeMean d : ℝ)

/-- Balanced-count hypothesis `d(x) ≍ N / n` with concrete lower and upper constants. -/
def microcanonicalBalancedCounts (d : α → ℕ) (cLower cUpper : ℝ) : Prop :=
  0 < cLower ∧
    cLower ≤ cUpper ∧
    ∀ x : α,
      cLower * (microcanonicalTotalMass d : ℝ) / microcanonicalTypeCountReal α ≤ (d x : ℝ) ∧
        (d x : ℝ) ≤ cUpper * (microcanonicalTotalMass d : ℝ) / microcanonicalTypeCountReal α

/-- The benchmark center `n log n`. -/
noncomputable def microcanonicalNlognCenter (_α : Type*) [Fintype _α] : ℝ :=
  microcanonicalTypeCountReal _α * Real.log (microcanonicalTypeCountReal _α)

/-- Finite-scale surrogate for the requirement `n log n = o(N)`. -/
def microcanonicalNlognScaleSeparation (d : α → ℕ) : Prop :=
  microcanonicalNlognCenter α ≤ (microcanonicalTotalMass d : ℝ)

/-- A linear-size window around the `n log n` benchmark for the exact mean. -/
def microcanonicalNlognMeanWindow (d : α → ℕ) (C1 C2 : ℝ) : Prop :=
  microcanonicalNlognCenter α - C1 * microcanonicalTypeCountReal α ≤
      microcanonicalCoverTimeMeanReal d ∧
    microcanonicalCoverTimeMeanReal d ≤
      microcanonicalNlognCenter α + C2 * microcanonicalTypeCountReal α

/-- Concrete `O_P(n)` surrogate stated directly with the exact tail formula. -/
def microcanonicalCoverTimeOPnConcentration (d : α → ℕ) : Prop :=
  ∃ K : ℝ,
    0 < K ∧
      ∀ s : ℝ,
        0 ≤ s →
          ∃ tLower tUpper : ℕ,
            microcanonicalNlognCenter α - (s + K) * microcanonicalTypeCountReal α ≤
                (tLower : ℝ) ∧
              (tUpper : ℝ) ≤
                  microcanonicalNlognCenter α + (s + K) * microcanonicalTypeCountReal α ∧
                Real.exp (-s) / 2 ≤ (microcanonicalCoverTimeTailFormula d tLower : ℝ) ∧
                  (microcanonicalCoverTimeTailFormula d tUpper : ℝ) ≤ Real.exp (-s)

end

/-- Paper label wrapper for the balanced microcanonical `n log n` cover-time scale.
    thm:pom-microcanonical-cover-time-nlogn-scale -/
noncomputable def paper_pom_microcanonical_cover_time_nlogn_scale : Prop := by
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
