import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part60acb-groupoid-dimension-overload`. -/
theorem paper_xi_time_part60acb_groupoid_dimension_overload {ι : Type*} [Fintype ι]
    (blockDim : ι -> Nat) (algebraDim kRank : Nat)
    (hDim : algebraDim = ∑ w : ι, blockDim w * blockDim w)
    (hRank : kRank = Fintype.card ι) :
    algebraDim = ∑ w : ι, blockDim w ^ 2 ∧ kRank = Fintype.card ι := by
  constructor
  · simpa [pow_two] using hDim
  · exact hRank

end Omega.Zeta
