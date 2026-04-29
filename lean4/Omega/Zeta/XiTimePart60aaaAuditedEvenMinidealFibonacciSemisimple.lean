import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The audited even windows used by the minimum-degeneracy ideal audit. -/
def xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_window : Fin 4 → ℕ
  | 0 => 6
  | 1 => 8
  | 2 => 10
  | 3 => 12

/-- The Fibonacci matrix size in the minimum-degeneracy block. -/
def xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_block_rank
    (i : Fin 4) : ℕ :=
  Nat.fib (xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_window i / 2)

/-- The number of matrix blocks in the audited minimum-degeneracy ideal. -/
def xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_block_count
    (i : Fin 4) : ℕ :=
  Nat.fib (xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_window i)

/-- The semisimple dimension of the audited matrix-block direct sum. -/
def xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_dimension
    (i : Fin 4) : ℕ :=
  xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_block_count i *
    xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_block_rank i ^ 2

/-- The center size of a finite direct sum of full matrix blocks is its block count. -/
def xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_center_size
    (i : Fin 4) : ℕ :=
  xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_block_count i

/-- Concrete audited-even-window semisimple Fibonacci block statement. -/
def xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_statement : Prop :=
  ∀ i : Fin 4,
    let m := xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_window i;
    let r := xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_block_rank i;
    let b := xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_block_count i;
    let d := xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_dimension i;
    let z := xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_center_size i;
      (m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12) ∧
      r = Nat.fib (m / 2) ∧
      b = Nat.fib m ∧
      d = b * r ^ 2 ∧
      z = b ∧
      (i = 0 → (r, b, d, z) = (2, 8, 32, 8)) ∧
      (i = 1 → (r, b, d, z) = (3, 21, 189, 21)) ∧
      (i = 2 → (r, b, d, z) = (5, 55, 1375, 55)) ∧
      (i = 3 → (r, b, d, z) = (8, 144, 9216, 144))

/-- Paper label: `prop:xi-time-part60aaa-audited-even-minideal-fibonacci-semisimple`. -/
theorem paper_xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple :
    xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_statement := by
  unfold xi_time_part60aaa_audited_even_minideal_fibonacci_semisimple_statement
  intro i
  fin_cases i <;> native_decide

end Omega.Zeta
