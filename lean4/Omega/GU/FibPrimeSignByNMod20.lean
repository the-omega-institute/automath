import Omega.GU.FibPrimePisano

namespace Omega.GU

/-- The explicit residue-class package already established in the Pisano-period module. -/
abbrev gut_fibprime_sign_by_n_mod20_law : Prop :=
  (Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1) ∧
    Nat.fib 7 % 5 = 3 ∧
    Nat.fib 11 % 5 = 4 ∧
    Nat.fib 13 % 5 = 3 ∧
    Nat.fib 17 % 5 = 2 ∧
    Nat.fib 11 % 11 = 1 ∧
    Nat.fib 7 % 7 = 6

/-- Paper label: `cor:gut-fibprime-sign-by-n-mod20`. -/
theorem paper_gut_fibprime_sign_by_n_mod20 : gut_fibprime_sign_by_n_mod20_law := by
  exact paper_fibprime_sign_by_n_mod20

end Omega.GU
