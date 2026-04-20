import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Zeta

open scoped BigOperators

/-- The Smith-prefix axis count at depth `1` is exactly the number of positive exponents, and at
the top depth the accumulated prefix value has already reached the total exponent sum.
    thm:xi-disc-ledger-axis-depth-smith -/
theorem paper_xi_disc_ledger_axis_depth_smith {m : Nat} (e : Fin m → Nat) :
    (Finset.univ.sum fun i => if 0 < e i then 1 else 0) = smithPrefixDelta e 1 ∧
      smithPrefixValue e (smithPrefixTop e) = Finset.univ.sum e := by
  constructor
  · unfold smithPrefixDelta
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Nat.succ_le_iff]
  · simpa using smithPrefixValue_eq_total_of_le_top e (smithPrefixTop e) le_rfl

end Omega.Zeta
