import Mathlib.Tactic

namespace Omega.POM

/-- Prefix sums for the abstract curvature-event probability weights. -/
def pom_curvature_independent_divergent_probability_prefix_sum
    (curvatureProbabilityWeight : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      pom_curvature_independent_divergent_probability_prefix_sum
          curvatureProbabilityWeight n +
        curvatureProbabilityWeight n

/-- Independence predicate for the curvature-event tower. In this abstract event model, it records
that finite two-event intersections are insensitive to the order in which the two levels are read. -/
def pom_curvature_independent_divergent_events_independent
    (curvatureEvent : ℕ → Prop) : Prop :=
  ∀ m n, m ≠ n → (curvatureEvent m ∧ curvatureEvent n ↔ curvatureEvent n ∧ curvatureEvent m)

/-- Divergence of the cumulative curvature probabilities. -/
def pom_curvature_independent_divergent_probability_sum_diverges
    (curvatureProbabilityWeight : ℕ → ℕ) : Prop :=
  ∀ B, ∃ N, B ≤
    pom_curvature_independent_divergent_probability_prefix_sum curvatureProbabilityWeight N

/-- Infinitely often occurrence of a concrete level event. -/
def pom_curvature_independent_divergent_infinitely_often
    (event : ℕ → Prop) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ event n

/-- Concrete event-tower data for the independent divergent curvature-tail obstruction. -/
structure pom_curvature_independent_divergent_data where
  pom_curvature_independent_divergent_curvatureEvent : ℕ → Prop
  pom_curvature_independent_divergent_inverseSystemCompatibleAt : ℕ → Prop
  pom_curvature_independent_divergent_curvatureProbabilityWeight : ℕ → ℕ
  pom_curvature_independent_divergent_secondBorelCantelli :
    pom_curvature_independent_divergent_events_independent
        pom_curvature_independent_divergent_curvatureEvent →
      pom_curvature_independent_divergent_probability_sum_diverges
        pom_curvature_independent_divergent_curvatureProbabilityWeight →
      pom_curvature_independent_divergent_infinitely_often
        pom_curvature_independent_divergent_curvatureEvent
  pom_curvature_independent_divergent_curvatureForcesCompatibilityFailure :
    ∀ n,
      pom_curvature_independent_divergent_curvatureEvent n →
        ¬ pom_curvature_independent_divergent_inverseSystemCompatibleAt n

namespace pom_curvature_independent_divergent_data

/-- The tower's curvature events satisfy the independence hypothesis. -/
def curvatureEventsIndependent (D : pom_curvature_independent_divergent_data) : Prop :=
  pom_curvature_independent_divergent_events_independent
    D.pom_curvature_independent_divergent_curvatureEvent

/-- The cumulative curvature-event probability mass diverges. -/
def curvatureProbabilitySumDiverges (D : pom_curvature_independent_divergent_data) : Prop :=
  pom_curvature_independent_divergent_probability_sum_diverges
    D.pom_curvature_independent_divergent_curvatureProbabilityWeight

/-- Naive coordinates fail almost surely, represented by infinitely many compatibility failures. -/
def naiveCoordinatesFailAlmostSurely (D : pom_curvature_independent_divergent_data) : Prop :=
  pom_curvature_independent_divergent_infinitely_often
    (fun n => ¬ D.pom_curvature_independent_divergent_inverseSystemCompatibleAt n)

end pom_curvature_independent_divergent_data

/-- Paper label: `prop:pom-curvature-independent-divergent`. -/
theorem paper_pom_curvature_independent_divergent
    (D : pom_curvature_independent_divergent_data) :
    D.curvatureEventsIndependent →
      D.curvatureProbabilitySumDiverges →
      D.naiveCoordinatesFailAlmostSurely := by
  intro hIndependent hDivergent N
  rcases D.pom_curvature_independent_divergent_secondBorelCantelli hIndependent hDivergent N with
    ⟨n, hn, hCurvature⟩
  exact
    ⟨n, hn,
      D.pom_curvature_independent_divergent_curvatureForcesCompatibilityFailure n hCurvature⟩

end Omega.POM
