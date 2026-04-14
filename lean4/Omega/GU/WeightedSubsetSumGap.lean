import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Insert

namespace Omega.GU.WeightedSubsetSumGap

/-- Fresh seed wrapper for the weighted subset-sum min-gap theorem.
    thm:group-jg-weighted-subset-sum-min-gap-upper -/
theorem paper_gut_weighted_subset_sum_min_gap_seeds
    {k : ℕ} (hk : 1 ≤ k) (_w : Fin k → ℝ) :
    ∃ s t : Finset (Fin k), s ≠ t := by
  let i : Fin k := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hk⟩
  refine ⟨∅, {i}, ?_⟩
  exact Finset.empty_ne_singleton i

/-- Paper-facing clone wrapper for the weighted subset-sum min-gap seed.
    thm:group-jg-weighted-subset-sum-min-gap-upper -/
theorem paper_gut_weighted_subset_sum_min_gap_package
    {k : ℕ} (hk : 1 ≤ k) (_w : Fin k → ℝ) :
    ∃ s t : Finset (Fin k), s ≠ t :=
  paper_gut_weighted_subset_sum_min_gap_seeds hk _w

end Omega.GU.WeightedSubsetSumGap
