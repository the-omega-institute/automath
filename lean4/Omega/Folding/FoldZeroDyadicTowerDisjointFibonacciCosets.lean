import Mathlib
import Omega.Folding.FoldZeroHalfIndexMultiple6

namespace Omega.Folding

/-- Along the sixfold subsequence, the first dyadic level of the fold-zero tower already contributes
the half-index Fibonacci coset supplied by the existing `S_g(M)` infrastructure. This gives the
concrete Fibonacci lower bound used as the base layer of the dyadic-tower argument. -/
theorem paper_xi_fold_zero_dyadic_tower_disjoint_fibonacci_cosets (m : ℕ)
    (hm : (m + 2) % 6 = 0) :
    Nat.fib ((m + 2) / 2) ∣ Nat.fib (m + 2) / 2 ∧
      Nat.fib ((m + 2) / 2) ≤ (foldZeroFrequencyUnion m).card := by
  simpa using paper_fold_zero_half_index_multiple6 m hm

end Omega.Folding
