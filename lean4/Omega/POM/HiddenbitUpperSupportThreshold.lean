import Mathlib.Tactic
import Omega.Folding.MomentBounds

namespace Omega

/-- Paper label: `prop:pom-hiddenbit-upper-support-threshold`. -/
theorem paper_pom_hiddenbit_upper_support_threshold (m : ℕ) (hm : 2 ≤ m) :
    (Finset.univ.filter (fun x : Omega.X m => 0 < Omega.fiberHiddenBitCount 1 x)).card =
      Nat.fib (m + 1) - 1 := by
  exact upper_support_card m hm

end Omega
