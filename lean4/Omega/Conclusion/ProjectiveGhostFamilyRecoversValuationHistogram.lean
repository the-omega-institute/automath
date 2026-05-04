import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Cumulative zero-residue count through valuation level `r`. -/
def conclusion_projective_ghost_family_recovers_valuation_histogram_zeroResidueCount
    (multiplicity : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∑ v ∈ Finset.range (r + 1), multiplicity v

/-- The cumulative valuation count recovered from the projective ghost tower. -/
def conclusion_projective_ghost_family_recovers_valuation_histogram_cumulativeCount
    (multiplicity : ℕ → ℕ) (r : ℕ) : ℕ :=
  conclusion_projective_ghost_family_recovers_valuation_histogram_zeroResidueCount
    multiplicity r

/-- Exact valuation bin reconstructed from adjacent cumulative counts. -/
def conclusion_projective_ghost_family_recovers_valuation_histogram_exactHistogram
    (multiplicity : ℕ → ℕ) : ℕ → ℕ
  | 0 =>
      conclusion_projective_ghost_family_recovers_valuation_histogram_zeroResidueCount
        multiplicity 0
  | r + 1 =>
      conclusion_projective_ghost_family_recovers_valuation_histogram_zeroResidueCount
          multiplicity (r + 1) -
        conclusion_projective_ghost_family_recovers_valuation_histogram_zeroResidueCount
          multiplicity r

/-- Newton-polygon horizontal coordinate reconstructed from exact histogram bins. -/
def conclusion_projective_ghost_family_recovers_valuation_histogram_recoveredNewtonX
    (multiplicity : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∑ v ∈ Finset.range r,
    conclusion_projective_ghost_family_recovers_valuation_histogram_exactHistogram
      multiplicity v

/-- Newton-polygon horizontal coordinate defined directly from the valuation histogram. -/
def conclusion_projective_ghost_family_recovers_valuation_histogram_newtonX
    (multiplicity : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∑ v ∈ Finset.range r, multiplicity v

/-- The projective ghost family recovers all cumulative counts. -/
def conclusion_projective_ghost_family_recovers_valuation_histogram_recoversCumulativeCounts
    (multiplicity : ℕ → ℕ) : Prop :=
  ∀ r,
    conclusion_projective_ghost_family_recovers_valuation_histogram_cumulativeCount
        multiplicity r =
      conclusion_projective_ghost_family_recovers_valuation_histogram_zeroResidueCount
        multiplicity r

/-- Adjacent differences recover each exact valuation bin. -/
def conclusion_projective_ghost_family_recovers_valuation_histogram_recoversExactHistogram
    (multiplicity : ℕ → ℕ) : Prop :=
  ∀ r,
    conclusion_projective_ghost_family_recovers_valuation_histogram_exactHistogram
        multiplicity r =
      multiplicity r

/-- The recovered exact bins recover the Newton-polygon horizontal coordinates. -/
def conclusion_projective_ghost_family_recovers_valuation_histogram_recoversNewtonPolygon
    (multiplicity : ℕ → ℕ) : Prop :=
  ∀ r,
    conclusion_projective_ghost_family_recovers_valuation_histogram_recoveredNewtonX
        multiplicity r =
      conclusion_projective_ghost_family_recovers_valuation_histogram_newtonX multiplicity r

lemma conclusion_projective_ghost_family_recovers_valuation_histogram_exactHistogram_eq
    (multiplicity : ℕ → ℕ) :
    conclusion_projective_ghost_family_recovers_valuation_histogram_recoversExactHistogram
      multiplicity := by
  intro r
  cases r with
  | zero =>
      simp [conclusion_projective_ghost_family_recovers_valuation_histogram_exactHistogram,
        conclusion_projective_ghost_family_recovers_valuation_histogram_zeroResidueCount]
  | succ r =>
      simp [conclusion_projective_ghost_family_recovers_valuation_histogram_exactHistogram,
        conclusion_projective_ghost_family_recovers_valuation_histogram_zeroResidueCount,
        Finset.sum_range_succ]

/-- Paper label: `thm:conclusion-projective-ghost-family-recovers-valuation-histogram`. -/
theorem paper_conclusion_projective_ghost_family_recovers_valuation_histogram
    (multiplicity : ℕ → ℕ) :
    conclusion_projective_ghost_family_recovers_valuation_histogram_recoversCumulativeCounts
        multiplicity ∧
      conclusion_projective_ghost_family_recovers_valuation_histogram_recoversExactHistogram
        multiplicity ∧
      conclusion_projective_ghost_family_recovers_valuation_histogram_recoversNewtonPolygon
        multiplicity := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rfl
  · exact conclusion_projective_ghost_family_recovers_valuation_histogram_exactHistogram_eq
      multiplicity
  · intro r
    unfold conclusion_projective_ghost_family_recovers_valuation_histogram_recoveredNewtonX
    unfold conclusion_projective_ghost_family_recovers_valuation_histogram_newtonX
    apply Finset.sum_congr rfl
    intro v _hv
    exact conclusion_projective_ghost_family_recovers_valuation_histogram_exactHistogram_eq
      multiplicity v

end Omega.Conclusion
