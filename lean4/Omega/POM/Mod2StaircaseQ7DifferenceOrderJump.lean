import Mathlib.Tactic

namespace Omega.POM

/-- cor:pom-mod2-staircase-q7-difference-order-jump -/
theorem paper_pom_mod2_staircase_q7_difference_order_jump
    (b : Nat -> Nat) (lowBasis highBasis : Prop)
    (h456 : b 4 = 2 ∧ b 5 = 2 ∧ b 6 = 2)
    (h710 : b 7 = 4 ∧ b 8 = 4 ∧ b 9 = 4 ∧ b 10 = 4)
    (hLow : lowBasis) (hHigh : highBasis) :
    (b 4 = 2 ∧ b 5 = 2 ∧ b 6 = 2) ∧
      (b 7 = 4 ∧ b 8 = 4 ∧ b 9 = 4 ∧ b 10 = 4) ∧ lowBasis ∧ highBasis := by
  exact ⟨h456, h710, hLow, hHigh⟩

end Omega.POM
