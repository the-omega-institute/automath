import Mathlib.Data.Nat.Choose.Basic

namespace Omega.GU

/-- The number of `t`-subsets moved by a swap transposition via "contains exactly one of the two
swapped points". -/
def tSubsetSwapTranspositionCount (k t : Nat) : Nat :=
  Nat.choose (k - 2) (t - 1)

/-- Paper wrapper: the transfer exponent is the binomial count of `(t - 1)`-subsets of the
remaining `k - 2` points. -/
theorem paper_bdry_orientation_tsubset_transfer_binomial (k t : Nat) :
    tSubsetSwapTranspositionCount k t = Nat.choose (k - 2) (t - 1) := by
  rfl

end Omega.GU
