import Omega.Core.Fib

namespace Omega.Zeta

/-- Paper label: `lem:gm-fibonacci-divisibility`. -/
theorem paper_gm_fibonacci_divisibility {a b : Nat} (hab : a ∣ b) :
    Nat.fib a ∣ Nat.fib b := by
  exact Nat.fib_dvd a b hab

end Omega.Zeta
