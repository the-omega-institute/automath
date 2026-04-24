import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete critical order for the fixed-order freezing model. -/
def xiTerminalFixedOrderCritical : ℕ := 1

/-- Maximal-fiber contribution. -/
def xiTerminalMaxContribution (a m : ℕ) : ℕ :=
  4 ^ (a * m)

/-- Off-maximal contribution. -/
def xiTerminalOffMaxContribution (a m : ℕ) : ℕ :=
  2 ^ (a * m)

/-- Total fixed-order sum split into maximal and off-maximal parts. -/
def xiTerminalFixedOrderSum (a m : ℕ) : ℕ :=
  xiTerminalMaxContribution a m + xiTerminalOffMaxContribution a m

lemma xiTerminalMaxContribution_le_sum (a m : ℕ) :
    xiTerminalMaxContribution a m ≤ xiTerminalFixedOrderSum a m := by
  unfold xiTerminalFixedOrderSum xiTerminalMaxContribution xiTerminalOffMaxContribution
  exact Nat.le_add_right _ _

lemma xiTerminalOffMaxContribution_le_max (a m : ℕ) :
    xiTerminalOffMaxContribution a m ≤ xiTerminalMaxContribution a m := by
  unfold xiTerminalMaxContribution xiTerminalOffMaxContribution
  have hmul : a * m ≤ 2 * (a * m) := by omega
  calc
    2 ^ (a * m) ≤ 2 ^ (2 * (a * m)) := Nat.pow_le_pow_right (by simp) hmul
    _ = (2 ^ 2) ^ (a * m) := by rw [pow_mul]
    _ = 4 ^ (a * m) := by norm_num

lemma xiTerminalFixedOrderSum_le_double_max (a m : ℕ) :
    xiTerminalFixedOrderSum a m ≤ 2 * xiTerminalMaxContribution a m := by
  unfold xiTerminalFixedOrderSum
  have hoff : xiTerminalOffMaxContribution a m ≤ xiTerminalMaxContribution a m :=
    xiTerminalOffMaxContribution_le_max a m
  omega

/-- Concrete freezing-threshold package: the total fixed-order sum is squeezed between the maximal
branch and twice the maximal branch, and above the critical order the off-maximal branch never
beats the maximal one.
    thm:xi-terminal-fixed-order-freezing-threshold -/
theorem paper_xi_terminal_fixed_order_freezing_threshold :
    (∀ a m : ℕ, xiTerminalMaxContribution a m ≤ xiTerminalFixedOrderSum a m) ∧
    (∀ a m : ℕ, xiTerminalFixedOrderCritical ≤ a →
      xiTerminalOffMaxContribution a m ≤ xiTerminalMaxContribution a m) ∧
    (∀ a m : ℕ, xiTerminalFixedOrderCritical ≤ a →
      xiTerminalFixedOrderSum a m ≤ 2 * xiTerminalMaxContribution a m) := by
  refine ⟨xiTerminalMaxContribution_le_sum, ?_, ?_⟩
  · intro a m _ha
    exact xiTerminalOffMaxContribution_le_max a m
  · intro a m _ha
    exact xiTerminalFixedOrderSum_le_double_max a m

end Omega.Zeta
