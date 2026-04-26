import Mathlib
import Omega.Zeta.XiBqPowerEntrywiseFibonacciBinomial

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_cq_power_boundary_and_row_sum_choose_factor
    (q k t : ℕ) (ht : t ∈ Finset.range (k + 1)) :
    Nat.choose q t * Nat.choose (q - t) (k - t) = Nat.choose q k * Nat.choose k t := by
  exact
    (Nat.choose_mul (n := q) (k := k) (s := t)
      (Nat.le_of_lt_succ (Finset.mem_range.mp ht))).symm

private lemma xi_cq_power_boundary_and_row_sum_coeff_closed_form
    (q m k : ℕ) :
    xiBqPowerEntrywiseCoeff q m k =
      Nat.choose q k * 2 ^ k * xiBqIteratedXCoeff m ^ (q - k) * xiBqIteratedYCoeff m ^ k := by
  unfold xiBqPowerEntrywiseCoeff xiBqPowerEntrywiseSummand
  calc
    ∑ t ∈ Finset.range (k + 1),
        Nat.choose q t * Nat.choose (q - t) (k - t) *
          xiBqIteratedXCoeff m ^ (q - k) * xiBqIteratedYCoeff m ^ k =
      ∑ t ∈ Finset.range (k + 1),
        (Nat.choose q k * Nat.choose k t) *
          xiBqIteratedXCoeff m ^ (q - k) * xiBqIteratedYCoeff m ^ k := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [xi_cq_power_boundary_and_row_sum_choose_factor q k t ht]
    _ = ∑ t ∈ Finset.range (k + 1),
        (Nat.choose q k * xiBqIteratedXCoeff m ^ (q - k) *
          xiBqIteratedYCoeff m ^ k) * Nat.choose k t := by
        apply Finset.sum_congr rfl
        intro t ht
        simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (Nat.choose q k * xiBqIteratedXCoeff m ^ (q - k) *
          xiBqIteratedYCoeff m ^ k) *
        ∑ t ∈ Finset.range (k + 1), Nat.choose k t := by
        rw [Finset.mul_sum]
    _ = (Nat.choose q k * xiBqIteratedXCoeff m ^ (q - k) *
          xiBqIteratedYCoeff m ^ k) *
        2 ^ k := by
        rw [Nat.sum_range_choose]
    _ = Nat.choose q k * 2 ^ k * xiBqIteratedXCoeff m ^ (q - k) *
        xiBqIteratedYCoeff m ^ k := by
        simp [mul_assoc, mul_left_comm, mul_comm]

private lemma xi_cq_power_boundary_and_row_sum_left_boundary
    (q m : ℕ) :
    xiBqPowerEntrywiseCoeff q m 0 = xiBqIteratedXCoeff m ^ q := by
  rw [xi_cq_power_boundary_and_row_sum_coeff_closed_form]
  simp

private lemma xi_cq_power_boundary_and_row_sum_right_boundary
    (q m : ℕ) :
    xiBqPowerEntrywiseCoeff q m q = 2 ^ q * xiBqIteratedYCoeff m ^ q := by
  rw [xi_cq_power_boundary_and_row_sum_coeff_closed_form]
  simp

private lemma xi_cq_power_boundary_and_row_sum_row_sum_formula
    (q m : ℕ) :
    ∑ k ∈ Finset.range (q + 1), xiBqPowerEntrywiseCoeff q m k =
      (xiBqIteratedXCoeff m + 2 * xiBqIteratedYCoeff m) ^ q := by
  calc
    ∑ k ∈ Finset.range (q + 1), xiBqPowerEntrywiseCoeff q m k =
      ∑ k ∈ Finset.range (q + 1),
        Nat.choose q k * xiBqIteratedXCoeff m ^ (q - k) *
          (2 * xiBqIteratedYCoeff m) ^ k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [xi_cq_power_boundary_and_row_sum_coeff_closed_form]
        have hpow :
            2 ^ k * xiBqIteratedYCoeff m ^ k = (2 * xiBqIteratedYCoeff m) ^ k := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_pow 2 (xiBqIteratedYCoeff m) k).symm
        calc
          Nat.choose q k * 2 ^ k * xiBqIteratedXCoeff m ^ (q - k) * xiBqIteratedYCoeff m ^ k =
              Nat.choose q k * xiBqIteratedXCoeff m ^ (q - k) *
                (2 ^ k * xiBqIteratedYCoeff m ^ k) := by
                  simp [mul_assoc, mul_left_comm]
          _ = Nat.choose q k * xiBqIteratedXCoeff m ^ (q - k) *
                (2 * xiBqIteratedYCoeff m) ^ k := by
                  rw [hpow]
    _ = (2 * xiBqIteratedYCoeff m + xiBqIteratedXCoeff m) ^ q := by
        symm
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (add_pow (2 * xiBqIteratedYCoeff m) (xiBqIteratedXCoeff m) q)
    _ = (xiBqIteratedXCoeff m + 2 * xiBqIteratedYCoeff m) ^ q := by
        rw [add_comm]

/-- Paper label: `cor:xi-Cq-power-boundary-and-row-sum`. Specializing the entrywise
Fibonacci/binomial formula to the two boundary indices gives the corner values, and summing the
row evaluates the generating polynomial at `(1, 1)`, leaving a single Fibonacci recurrence
rewrite. -/
def paper_xi_cq_power_boundary_and_row_sum_statement : Prop :=
  (∀ q m : ℕ, xiBqPowerEntrywiseCoeff q m 0 = xiBqIteratedXCoeff m ^ q) ∧
    (∀ q m : ℕ, xiBqPowerEntrywiseCoeff q m q = 2 ^ q * xiBqIteratedYCoeff m ^ q) ∧
    (∀ q m : ℕ,
      ∑ k ∈ Finset.range (q + 1), xiBqPowerEntrywiseCoeff q m k =
        (xiBqIteratedXCoeff (m + 1) + xiBqIteratedYCoeff m) ^ q)

theorem paper_xi_cq_power_boundary_and_row_sum :
    paper_xi_cq_power_boundary_and_row_sum_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro q m
    exact xi_cq_power_boundary_and_row_sum_left_boundary q m
  · intro q m
    exact xi_cq_power_boundary_and_row_sum_right_boundary q m
  · intro q m
    have hfib :=
      (paper_xi_bq_power_entrywise_fibonacci_binomial q m 0 0).1
    calc
      ∑ k ∈ Finset.range (q + 1), xiBqPowerEntrywiseCoeff q m k =
          (xiBqIteratedXCoeff m + 2 * xiBqIteratedYCoeff m) ^ q :=
        xi_cq_power_boundary_and_row_sum_row_sum_formula q m
      _ = (xiBqIteratedXCoeff (m + 1) + xiBqIteratedYCoeff m) ^ q := by
        rw [hfib, two_mul]
        simp [add_left_comm, add_comm]

end Omega.Zeta
