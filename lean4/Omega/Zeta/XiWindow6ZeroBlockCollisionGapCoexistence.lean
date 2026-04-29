import Omega.Folding.FoldZeroHalfIndexMultiple6
import Omega.Zeta.XiFoldFibonacciCollisionGapPositiveFloor

namespace Omega.Zeta

/-- Paper label: `cor:xi-window6-zero-block-and-collision-gap-coexistence`. -/
theorem paper_xi_window6_zero_block_and_collision_gap_coexistence (m : ℕ)
    (hm : (m + 2) % 6 = 0) (Cphi : Real) :
    Nat.fib ((m + 2) / 2) ≤ (Omega.Folding.foldZeroFrequencyUnion m).card ∧
      Omega.Zeta.XiFoldFibonacciCollisionGapPositiveFloor Cphi := by
  exact ⟨(Omega.Folding.paper_fold_zero_half_index_multiple6 m hm).2,
    Omega.Zeta.paper_xi_fold_fibonacci_collision_gap_positive_floor Cphi⟩

end Omega.Zeta
