import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.GU.Window6DyadicBudget

/-- Window-6 dyadic budget: 2^6 = (15+3+3) + (34+8+1).
    prop:window6-dyadic-budget-three-stage -/
theorem paper_gut_window6_dyadic_budget_three_stage :
    (2 ^ 6 = (15 + 3 + 3) + (34 + 8 + 1)) ∧
    (Nat.fib 8 = 21) ∧ (Nat.fib 9 = 34) ∧
    (Nat.fib 6 = 8) ∧ (Nat.fib 2 = 1) ∧
    (2 ^ 6 - Nat.fib 8 = 43) ∧
    (Nat.fib 9 + Nat.fib 6 + Nat.fib 2 = 43) ∧
    (15 + 3 + 3 = Nat.fib 8) ∧
    (Nat.fib 8 + 43 = 2 ^ 6) := by
  norm_num [Nat.fib_add_two]

end Omega.GU.Window6DyadicBudget
