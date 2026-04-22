import Mathlib.Tactic

namespace Omega.Discussion

/-- Concrete threshold data for the negative-count discussion package. The function
`negativeCount N` records the number of negative Toeplitz directions visible at scale `N`, while
`ambientCount N` is the total candidate count at that scale. Past `thresholdN` the count
stabilizes to the full ambient value, whereas at `smallN` there is still a missing direction. -/
structure ToeplitzNegativeCountThresholdData where
  thresholdN : ℕ
  largeN : ℕ
  smallN : ℕ
  negativeCount : ℕ → ℕ
  ambientCount : ℕ → ℕ
  largeN_ge_threshold : thresholdN ≤ largeN
  smallN_lt_threshold : smallN < thresholdN
  stabilization :
    ∀ N ≥ thresholdN, negativeCount N = ambientCount N
  unresolvedMode :
    negativeCount smallN < ambientCount smallN

namespace ToeplitzNegativeCountThresholdData

/-- Beyond the stabilization threshold the Toeplitz truncation exhibits the full negative count. -/
def largeNFullNegativeCount (D : ToeplitzNegativeCountThresholdData) : Prop :=
  D.negativeCount D.largeN = D.ambientCount D.largeN

/-- Below threshold one negative direction is still missing. -/
def smallNMissingNegativeDirection (D : ToeplitzNegativeCountThresholdData) : Prop :=
  D.negativeCount D.smallN < D.ambientCount D.smallN

end ToeplitzNegativeCountThresholdData

open ToeplitzNegativeCountThresholdData

/-- Unpacking the large-`N` stabilization hypothesis and the small-`N` unresolved-mode witness
recovers the threshold dichotomy for Toeplitz negative counts.
    con:discussion-toeplitz-negative-count-threshold -/
theorem paper_discussion_toeplitz_negative_count_threshold
    (D : ToeplitzNegativeCountThresholdData) :
    D.largeNFullNegativeCount ∧ D.smallNMissingNegativeDirection := by
  refine ⟨?_, D.unresolvedMode⟩
  exact D.stabilization D.largeN D.largeN_ge_threshold

end Omega.Discussion
