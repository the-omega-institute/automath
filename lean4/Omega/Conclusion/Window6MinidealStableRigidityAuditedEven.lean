import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The audited even windows in the window-6 minimum-ideal stability audit. -/
def conclusion_window6_minideal_stable_rigidity_audited_even_audited_even
    (m : ℕ) : Prop :=
  m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12

/-- Stable classes are encoded by the Fibonacci multiplicity of the audited window. -/
def conclusion_window6_minideal_stable_rigidity_audited_even_stable_class
    (m : ℕ) : ℕ :=
  Nat.fib m

/-- On audited even windows, equality of stable classes is equality of windows. -/
def conclusion_window6_minideal_stable_rigidity_audited_even_statement
    (m n : ℕ) : Prop :=
  conclusion_window6_minideal_stable_rigidity_audited_even_stable_class m =
      conclusion_window6_minideal_stable_rigidity_audited_even_stable_class n ↔
    m = n

/-- Paper label:
`cor:conclusion-window6-minideal-stable-rigidity-audited-even`. -/
theorem paper_conclusion_window6_minideal_stable_rigidity_audited_even (m n : ℕ)
    (hm : conclusion_window6_minideal_stable_rigidity_audited_even_audited_even m)
    (hn : conclusion_window6_minideal_stable_rigidity_audited_even_audited_even n) :
    conclusion_window6_minideal_stable_rigidity_audited_even_statement m n := by
  rcases hm with rfl | rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl | rfl <;>
      unfold conclusion_window6_minideal_stable_rigidity_audited_even_statement
        conclusion_window6_minideal_stable_rigidity_audited_even_stable_class <;>
      native_decide

end Omega.Conclusion
