import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

noncomputable section

/-- Concrete RH-sharp parity data: a main Perron scale `λ`, a sign `ε ∈ {±1}`, and an exact
decomposition of the trace sequence into the leading two oscillatory channels plus an error term. -/
structure finite_rh_parity_general_data where
  lam : ℝ
  eps : ℝ
  a : ℕ → ℝ
  err : ℕ → ℝ
  heps : eps = 1 ∨ eps = -1
  a_decomposition :
    ∀ n : ℕ, a n = lam ^ n + eps ^ n * lam ^ (n / 2) + err n

/-- The primitive orbit count obtained from the Witt/Möbius inversion of `a`. -/
def finite_rh_parity_general_primitive_count (D : finite_rh_parity_general_data) (n : ℕ) : ℝ :=
  (Finset.sum n.divisors fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) / n

/-- The odd-divisor tail after isolating the `d = 1` term. -/
def finite_rh_parity_general_odd_tail (D : finite_rh_parity_general_data) (n : ℕ) : ℝ :=
  Finset.sum (n.divisors.erase 1) fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)

/-- The even-divisor tail after isolating the `d = 1` and `d = 2` contributions. -/
def finite_rh_parity_general_even_tail (D : finite_rh_parity_general_data) (n : ℕ) : ℝ :=
  Finset.sum ((n.divisors.erase 1).erase 2) fun d =>
    (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)

/-- The odd-parity residual after separating the Perron term and the square-root oscillation. -/
def finite_rh_parity_general_odd_error (D : finite_rh_parity_general_data) (n : ℕ) : ℝ :=
  D.err n + finite_rh_parity_general_odd_tail D n

/-- The even-parity residual after the exact `d = 1, 2` cancellation at the `λ^(n/2)` scale. -/
def finite_rh_parity_general_even_error (D : finite_rh_parity_general_data) (n : ℕ) : ℝ :=
  D.err n - D.eps ^ (n / 2) * D.lam ^ (n / 4) - D.err (n / 2) +
    finite_rh_parity_general_even_tail D n

/-- Paper-facing parity cancellation law: odd lengths retain the square-root channel, while even
lengths lose it after the exact Möbius `d = 1, 2` cancellation. -/
def finite_rh_parity_general_data.parity_cancellation_law
    (D : finite_rh_parity_general_data) : Prop :=
  (∀ n : ℕ, 0 < n → Odd n →
    finite_rh_parity_general_primitive_count D n =
      D.lam ^ n / n + D.eps ^ n * D.lam ^ (n / 2) / n +
        finite_rh_parity_general_odd_error D n / n) ∧
  (∀ n : ℕ, 0 < n → Even n →
    finite_rh_parity_general_primitive_count D n =
      D.lam ^ n / n + finite_rh_parity_general_even_error D n / n)

/-- Paper label: `prop:finite-rh-parity-general`. -/
theorem paper_finite_rh_parity_general (D : finite_rh_parity_general_data) :
    D.parity_cancellation_law := by
  constructor
  · intro n hn hodd
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h1 : 1 ∈ n.divisors := by
      simp [Nat.mem_divisors, hn.ne']
    have hsum :
        Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) =
          D.a n + finite_rh_parity_general_odd_tail D n := by
      calc
        Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d))
            =
              Finset.sum (n.divisors.erase 1)
                (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) +
                (ArithmeticFunction.moebius 1 : ℝ) * D.a (n / 1) := by
                  simpa using
                    (Finset.sum_erase_add (s := n.divisors)
                      (f := fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) h1).symm
        _ = D.a n + finite_rh_parity_general_odd_tail D n := by
              unfold finite_rh_parity_general_odd_tail
              simp [hn.ne', add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    have hsplit :
        finite_rh_parity_general_primitive_count D n =
          (D.a n + finite_rh_parity_general_odd_tail D n) / n := by
      unfold finite_rh_parity_general_primitive_count
      rw [hsum]
    calc
      finite_rh_parity_general_primitive_count D n
          = (D.a n + finite_rh_parity_general_odd_tail D n) / n := hsplit
      _ = (D.lam ^ n + D.eps ^ n * D.lam ^ (n / 2) + D.err n +
            finite_rh_parity_general_odd_tail D n) / n := by
          rw [D.a_decomposition n]
      _ = D.lam ^ n / n + D.eps ^ n * D.lam ^ (n / 2) / n +
            finite_rh_parity_general_odd_error D n / n := by
          unfold finite_rh_parity_general_odd_error
          field_simp [hn0]
          ring
  · intro n hn hEven
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have h1 : 1 ∈ n.divisors := by
      simp [Nat.mem_divisors, hn.ne']
    have h2 : 2 ∈ n.divisors := by
      simp [Nat.mem_divisors, hn.ne', hEven.two_dvd]
    have h2erase : 2 ∈ n.divisors.erase 1 := by
      simp [h2]
    have hsum1 :
        Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) =
          D.a n +
            Finset.sum (n.divisors.erase 1)
              (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) := by
      calc
        Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d))
            =
              Finset.sum (n.divisors.erase 1)
                (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) +
                (ArithmeticFunction.moebius 1 : ℝ) * D.a (n / 1) := by
                  simpa using
                    (Finset.sum_erase_add (s := n.divisors)
                      (f := fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) h1).symm
        _ = D.a n +
              Finset.sum (n.divisors.erase 1)
                (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) := by
              simp [hn.ne', add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    have hsum2 :
        Finset.sum (n.divisors.erase 1) (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) =
          -(D.a (n / 2)) + finite_rh_parity_general_even_tail D n := by
      have hmu2_int : ArithmeticFunction.moebius 2 = -1 := by
        native_decide
      have hmu2 : (ArithmeticFunction.moebius 2 : ℝ) = -1 := by
        exact_mod_cast hmu2_int
      calc
        Finset.sum (n.divisors.erase 1) (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d))
            =
              Finset.sum ((n.divisors.erase 1).erase 2)
                (fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d)) +
                (ArithmeticFunction.moebius 2 : ℝ) * D.a (n / 2) := by
                  simpa using
                    (Finset.sum_erase_add (s := n.divisors.erase 1)
                      (f := fun d => (ArithmeticFunction.moebius d : ℝ) * D.a (n / d))
                      h2erase).symm
        _ = -(D.a (n / 2)) + finite_rh_parity_general_even_tail D n := by
              unfold finite_rh_parity_general_even_tail
              simp [hmu2, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    have hsplit :
        finite_rh_parity_general_primitive_count D n =
          (D.a n - D.a (n / 2) + finite_rh_parity_general_even_tail D n) / n := by
      unfold finite_rh_parity_general_primitive_count
      rw [hsum1, hsum2]
      ring
    have heps_sq : D.eps ^ 2 = 1 := by
      rcases D.heps with heps | heps <;> rw [heps] <;> norm_num
    have heps_even : D.eps ^ n = 1 := by
      rcases hEven with ⟨k, rfl⟩
      simpa [two_mul] using show D.eps ^ (2 * k) = 1 by
        rw [pow_mul, heps_sq]
        norm_num
    have hquarter : (n / 2) / 2 = n / 4 := by
      omega
    calc
      finite_rh_parity_general_primitive_count D n
          = (D.a n - D.a (n / 2) + finite_rh_parity_general_even_tail D n) / n := hsplit
      _ = (D.lam ^ n + D.eps ^ n * D.lam ^ (n / 2) + D.err n -
            (D.lam ^ (n / 2) + D.eps ^ (n / 2) * D.lam ^ (n / 4) + D.err (n / 2)) +
            finite_rh_parity_general_even_tail D n) / n := by
          rw [D.a_decomposition n, D.a_decomposition (n / 2), hquarter]
      _ = (D.lam ^ n + D.err n - D.eps ^ (n / 2) * D.lam ^ (n / 4) - D.err (n / 2) +
            finite_rh_parity_general_even_tail D n) / n := by
          rw [heps_even]
          ring
      _ = D.lam ^ n / n + finite_rh_parity_general_even_error D n / n := by
          unfold finite_rh_parity_general_even_error
          field_simp [hn0]
          ring

end

end Omega.SyncKernelWeighted
