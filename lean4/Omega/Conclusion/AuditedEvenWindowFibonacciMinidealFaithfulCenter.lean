import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The audited even windows `6, 8, 10, 12`. -/
def conclusion_audited_even_window_fibonacci_minideal_faithful_center_window :
    Fin 4 → ℕ
  | 0 => 6
  | 1 => 8
  | 2 => 10
  | 3 => 12

/-- Minimal block-ideal dimension in the audited Fibonacci normalization. -/
def conclusion_audited_even_window_fibonacci_minideal_faithful_center_minideal_dim
    (i : Fin 4) : ℕ :=
  Nat.fib (conclusion_audited_even_window_fibonacci_minideal_faithful_center_window i)

/-- Center dimension in the audited Fibonacci normalization. -/
def conclusion_audited_even_window_fibonacci_minideal_faithful_center_center_dim
    (i : Fin 4) : ℕ :=
  Nat.fib (conclusion_audited_even_window_fibonacci_minideal_faithful_center_window i + 1)

/-- Faithful direct-sum dimension in the audited Fibonacci normalization. -/
def conclusion_audited_even_window_fibonacci_minideal_faithful_center_faithful_dim
    (i : Fin 4) : ℕ :=
  Nat.fib (conclusion_audited_even_window_fibonacci_minideal_faithful_center_window i + 2)

/-- Paper-facing finite audit for the four even windows. -/
def conclusion_audited_even_window_fibonacci_minideal_faithful_center_statement : Prop :=
  ∀ i : Fin 4,
    let m := conclusion_audited_even_window_fibonacci_minideal_faithful_center_window i
    let block :=
      conclusion_audited_even_window_fibonacci_minideal_faithful_center_minideal_dim i
    let center :=
      conclusion_audited_even_window_fibonacci_minideal_faithful_center_center_dim i
    let faithful :=
      conclusion_audited_even_window_fibonacci_minideal_faithful_center_faithful_dim i
    (m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12) ∧
      block = Nat.fib m ∧
      center = Nat.fib (m + 1) ∧
      faithful = Nat.fib (m + 2) ∧
      block + center = faithful ∧
      (i = 0 → (block, center, faithful) = (8, 13, 21)) ∧
      (i = 1 → (block, center, faithful) = (21, 34, 55)) ∧
      (i = 2 → (block, center, faithful) = (55, 89, 144)) ∧
      (i = 3 → (block, center, faithful) = (144, 233, 377))

/-- Paper label:
`thm:conclusion-audited-even-window-fibonacci-minideal-faithful-center`. -/
theorem paper_conclusion_audited_even_window_fibonacci_minideal_faithful_center :
    conclusion_audited_even_window_fibonacci_minideal_faithful_center_statement := by
  unfold conclusion_audited_even_window_fibonacci_minideal_faithful_center_statement
  intro i
  fin_cases i <;> native_decide

end Omega.Conclusion
