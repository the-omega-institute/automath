import Mathlib.Tactic
import Omega.Folding.MomentBounds

namespace Omega

/-- Paper label: `cor:pom-hiddenbit-upper-support-m6-12`. -/
theorem paper_pom_hiddenbit_upper_support_m6_12 :
    (Finset.univ.filter (fun x : Omega.X 6 => 0 < Omega.fiberHiddenBitCount 1 x)).card = 12 := by
  simpa [Nat.fib] using upper_support_card 6 (by omega)

end Omega
