import Omega.Folding.ZeckendorfSignature

namespace Omega.GroupUnification

/-- Paper-facing arithmetic packaging of the family-uplift lock at `N_f = 2, 3, 4`.
    thm:terminal-family-uplift-lock -/
theorem paper_terminal_family_uplift_lock :
    15 * 2 = Nat.fib 8 + Nat.fib 6 + Nat.fib 2 ∧
      15 * 3 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 ∧
      15 * 4 = Nat.fib 10 + Nat.fib 5 := by
  simpa using Omega.ZeckSig.family_lock_zeckendorf

end Omega.GroupUnification
