import Omega.Core.Fib

namespace Omega.EA

/-- Paper-facing wrapper for Fibonacci divisibility, retaining the low-index side condition.
    Paper label: `lem:fib-divisibility-iff`. -/
theorem paper_fib_divisibility_iff (a b : Nat) (ha : 3 ≤ a) :
    Nat.fib a ∣ Nat.fib b ↔ a ∣ b := by
  exact Omega.fib_dvd_iff a b ha

end Omega.EA
