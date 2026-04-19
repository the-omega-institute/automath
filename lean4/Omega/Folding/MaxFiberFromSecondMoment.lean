import Omega.Folding.MomentSum

namespace Omega

/-- The second moment is bounded by the number of stable states times the square of the maximal
fiber multiplicity.
    prop:fold-maxfiber-from-second-moment -/
theorem paper_fold_maxfiber_from_second_moment (m : Nat) :
    momentSum 2 m ≤ Nat.fib (m + 2) * X.maxFiberMultiplicity m ^ 2 := by
  unfold momentSum
  calc
    ∑ x : X m, X.fiberMultiplicity x ^ 2
      ≤ ∑ _x : X m, X.maxFiberMultiplicity m ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact Nat.pow_le_pow_left (X.fiberMultiplicity_le_max x) 2
    _ = Nat.fib (m + 2) * X.maxFiberMultiplicity m ^ 2 := by
          simp [X.card_eq_fib]

end Omega
