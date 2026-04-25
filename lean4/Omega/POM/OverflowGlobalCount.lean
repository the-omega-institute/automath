import Omega.Folding.MaxFiberTwoStep

namespace Omega.POM

/-- The paper's global overflow count is the audited hidden-bit count from the folding model.
    `thm:pom-overflow-global-count` -/
def pom_overflow_global_count_count (m : ℕ) : ℕ :=
  Omega.hiddenBitCount m

/-- Two-step recurrence for the global overflow count.
    `thm:pom-overflow-global-count` -/
lemma pom_overflow_global_count_recurrence (m : ℕ) :
    pom_overflow_global_count_count (m + 2) = 2 ^ m + pom_overflow_global_count_count m := by
  simpa [pom_overflow_global_count_count] using Omega.hiddenBitCount_recurrence m

/-- Paper label: `thm:pom-overflow-global-count`. The global overflow bit count satisfies the same
two-step recurrence as the hidden-bit count and therefore has the exact floor form
`⌊2^m / 3⌋ = 2^m / 3` in natural-number division. -/
theorem paper_pom_overflow_global_count (m : ℕ) :
    pom_overflow_global_count_count m = 2 ^ m / 3 := by
  simpa [pom_overflow_global_count_count] using Omega.hiddenBitCount_floor_div_three m

end Omega.POM
