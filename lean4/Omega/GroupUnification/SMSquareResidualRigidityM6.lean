import Mathlib.Tactic
import Omega.Folding.ZeckendorfSignature

namespace Omega.GroupUnification

/-- The square-residual identity is rigid at `m = 6`: the audited `m = 6` case works, while the
Fibonacci square bound rules out every `m ≥ 7`.
    thm:sm-square-residual-rigidity-m6 -/
theorem paper_sm_square_residual_rigidity_m6 {m : ℕ} (hm : 6 ≤ m) :
    Nat.fib (m + 2) - 12 = Nat.fib (m - 2) ^ 2 ↔ m = 6 := by
  constructor
  · intro h
    exact Omega.ZeckSig.sm_square_residual_rigidity_m6 m hm h
  · intro h
    subst h
    native_decide

end Omega.GroupUnification
