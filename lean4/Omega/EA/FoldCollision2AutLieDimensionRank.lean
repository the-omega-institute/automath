import Omega.Folding.MomentTriple

namespace Omega.EA

/-- Paper-facing wrapper for the second collision moment sandwich and first difference audit.
    thm:fold-collision2-aut-lie-dimension-rank -/
theorem paper_fold_collision2_aut_lie_dimension_rank (m : Nat) :
    (Nat.fib (m + 2) ≤ Omega.momentSum 2 m ∧
      Omega.momentSum 2 m ≤ Omega.X.maxFiberMultiplicity m * 2 ^ m) ∧
    (Omega.momentSum 2 1 - Omega.momentSum 2 0 = 1 ∧
      Omega.momentSum 2 2 - Omega.momentSum 2 1 = 4 ∧
      Omega.momentSum 2 3 - Omega.momentSum 2 2 = 8) := by
  exact ⟨Omega.paper_momentSum_two_fibonacci_sandwich m,
    Omega.paper_momentSum_two_diff_values.1,
    Omega.paper_momentSum_two_diff_values.2.1,
    Omega.paper_momentSum_two_diff_values.2.2.1⟩

end Omega.EA
