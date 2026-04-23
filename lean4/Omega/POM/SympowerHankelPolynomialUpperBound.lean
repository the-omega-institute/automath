import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-sympower-hankel-polynomial-upper-bound`.
If the occupancy-vector quotient of the `q`-fold collision kernel has at most
`choose (q + N - 1) (N - 1)` states, Cayley-Hamilton bounds the recurrence order by that same
quantity, and both the Hankel rank and the minimal realization dimension are dominated by the
recurrence order, then both invariants are bounded by the same polynomial state-count. -/
theorem paper_pom_sympower_hankel_polynomial_upper_bound
    (q N hankelRank recurrenceOrder minimalRealizationDim : ℕ)
    (hQuotient :
      recurrenceOrder ≤ Nat.choose (q + N - 1) (N - 1))
    (hHankel :
      hankelRank ≤ recurrenceOrder)
    (hMinimal :
      minimalRealizationDim ≤ hankelRank) :
    hankelRank ≤ Nat.choose (q + N - 1) (N - 1) ∧
      minimalRealizationDim ≤ Nat.choose (q + N - 1) (N - 1) := by
  refine ⟨le_trans hHankel hQuotient, ?_⟩
  exact le_trans hMinimal (le_trans hHankel hQuotient)

end Omega.POM
