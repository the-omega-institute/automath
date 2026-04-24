import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.CapacityFiniteCompleteness

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite data for the fixed-resolution equivalence between the multiplicity histogram,
tail counts, continuous-capacity samples, and positive moment tower. -/
structure ConclusionTailCapacityMomentTailLawEquivalenceData where
  conclusion_tail_capacity_moment_tail_law_equivalence_α : Type
  conclusion_tail_capacity_moment_tail_law_equivalence_instFintype :
    Fintype conclusion_tail_capacity_moment_tail_law_equivalence_α
  conclusion_tail_capacity_moment_tail_law_equivalence_instDecidableEq :
    DecidableEq conclusion_tail_capacity_moment_tail_law_equivalence_α
  conclusion_tail_capacity_moment_tail_law_equivalence_multiplicity :
    conclusion_tail_capacity_moment_tail_law_equivalence_α → ℕ

attribute [instance]
  ConclusionTailCapacityMomentTailLawEquivalenceData.conclusion_tail_capacity_moment_tail_law_equivalence_instFintype

attribute [instance]
  ConclusionTailCapacityMomentTailLawEquivalenceData.conclusion_tail_capacity_moment_tail_law_equivalence_instDecidableEq

/-- The fixed-resolution finite-support package asserting that the exact multiplicity histogram,
the tail counts, the continuous-capacity samples, and the moment sums determine one another. -/
def ConclusionTailCapacityMomentTailLawEquivalenceData.Holds
    (D : ConclusionTailCapacityMomentTailLawEquivalenceData) : Prop :=
  let h : ℕ → ℕ := fun k =>
    Fintype.card
      {x : D.conclusion_tail_capacity_moment_tail_law_equivalence_α //
        D.conclusion_tail_capacity_moment_tail_law_equivalence_multiplicity x = k}
  let N : ℕ → ℕ := fun t =>
    Fintype.card
      {x : D.conclusion_tail_capacity_moment_tail_law_equivalence_α //
        t ≤ D.conclusion_tail_capacity_moment_tail_law_equivalence_multiplicity x}
  let C : ℕ → ℕ := fun t =>
    Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve
      D.conclusion_tail_capacity_moment_tail_law_equivalence_multiplicity t
  let S : ℕ → ℕ := fun q =>
    Finset.sum (Finset.univ :
      Finset D.conclusion_tail_capacity_moment_tail_law_equivalence_α) fun x =>
      D.conclusion_tail_capacity_moment_tail_law_equivalence_multiplicity x ^ q
  FiniteMultiplicityDataEquivalent (X := D.conclusion_tail_capacity_moment_tail_law_equivalence_α)
    h N C S

/-- Paper label: `thm:conclusion-tail-capacity-moment-tail-law-equivalence`. For fixed
resolution, the already verified finite-support completeness package identifies the exact
multiplicity histogram with the tail counts, the continuous-capacity curve, and the full positive
moment tower. -/
theorem paper_conclusion_tail_capacity_moment_tail_law_equivalence
    (D : ConclusionTailCapacityMomentTailLawEquivalenceData) : D.Holds := by
  simpa [ConclusionTailCapacityMomentTailLawEquivalenceData.Holds] using
    (paper_conclusion_capacity_finite_completeness
      (X := D.conclusion_tail_capacity_moment_tail_law_equivalence_α)
      D.conclusion_tail_capacity_moment_tail_law_equivalence_multiplicity)

end Omega.Conclusion
