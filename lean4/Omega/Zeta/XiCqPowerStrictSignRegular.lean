import Mathlib
import Omega.Zeta.XiBqPowerEntrywiseFibonacciBinomial

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_cq_power_strict_sign_regular_choose_factor
    (q k t : ℕ) (ht : t ∈ Finset.range (k + 1)) :
    Nat.choose q t * Nat.choose (q - t) (k - t) = Nat.choose q k * Nat.choose k t := by
  exact
    (Nat.choose_mul (n := q) (k := k) (s := t)
      (Nat.le_of_lt_succ (Finset.mem_range.mp ht))).symm

private lemma xi_cq_power_strict_sign_regular_coeff_closed_form
    (q m k : ℕ) :
    xiBqPowerEntrywiseCoeff q m k =
      Nat.choose q k * 2 ^ k * xiBqIteratedXCoeff m ^ (q - k) *
        xiBqIteratedYCoeff m ^ k := by
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
        rw [xi_cq_power_strict_sign_regular_choose_factor q k t ht]
    _ = ∑ t ∈ Finset.range (k + 1),
        (Nat.choose q k * xiBqIteratedXCoeff m ^ (q - k) *
          xiBqIteratedYCoeff m ^ k) * Nat.choose k t := by
        apply Finset.sum_congr rfl
        intro t _ht
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

private lemma xi_cq_power_strict_sign_regular_x_pos (m : ℕ) :
    0 < xiBqIteratedXCoeff m := by
  unfold xiBqIteratedXCoeff
  exact Nat.fib_pos.mpr (Nat.succ_pos m)

private lemma xi_cq_power_strict_sign_regular_y_pos {m : ℕ} (hm : 0 < m) :
    0 < xiBqIteratedYCoeff m := by
  unfold xiBqIteratedYCoeff
  exact Nat.fib_pos.mpr hm

private lemma xi_cq_power_strict_sign_regular_coeff_pos
    (q m k : ℕ) (hm : 0 < m) (hk : k ≤ q) :
    0 < xiBqPowerEntrywiseCoeff q m k := by
  rw [xi_cq_power_strict_sign_regular_coeff_closed_form]
  exact
    Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos (Nat.choose_pos hk) (pow_pos (by norm_num : 0 < (2 : ℕ)) k))
        (pow_pos (xi_cq_power_strict_sign_regular_x_pos m) (q - k)))
      (pow_pos (xi_cq_power_strict_sign_regular_y_pos hm) k)

/-- The alternating sign attached to the `k`-th reversed Pascal layer. -/
def xi_cq_power_strict_sign_regular_sign (k : ℕ) : ℤ :=
  if Even k then 1 else -1

/-- The target-local signed Pascal/reversal base entry. -/
def xi_cq_power_strict_sign_regular_base_entry (q k : ℕ) : ℤ :=
  xi_cq_power_strict_sign_regular_sign k * (Nat.choose q k : ℤ)

/-- The target-local signed coefficient extracted from the Fibonacci-binomial power formula. -/
def xi_cq_power_strict_sign_regular_signed_entry (q m k : ℕ) : ℤ :=
  xi_cq_power_strict_sign_regular_sign k * (xiBqPowerEntrywiseCoeff q m k : ℤ)

private lemma xi_cq_power_strict_sign_regular_sign_sq (k : ℕ) :
    xi_cq_power_strict_sign_regular_sign k * xi_cq_power_strict_sign_regular_sign k = 1 := by
  by_cases hk : Even k <;> simp [xi_cq_power_strict_sign_regular_sign, hk]

private lemma xi_cq_power_strict_sign_regular_base_sign
    (q k : ℕ) (hk : k ≤ q) :
    0 < xi_cq_power_strict_sign_regular_sign k *
      xi_cq_power_strict_sign_regular_base_entry q k := by
  have hchoose : (0 : ℤ) < (Nat.choose q k : ℤ) := by
    exact_mod_cast Nat.choose_pos hk
  rw [xi_cq_power_strict_sign_regular_base_entry, ← mul_assoc,
    xi_cq_power_strict_sign_regular_sign_sq]
  simpa using hchoose

private lemma xi_cq_power_strict_sign_regular_signed_entry_sign
    (q m k : ℕ) (hm : 0 < m) (hk : k ≤ q) :
    0 < xi_cq_power_strict_sign_regular_sign k *
      xi_cq_power_strict_sign_regular_signed_entry q m k := by
  have hcoeff : (0 : ℤ) < (xiBqPowerEntrywiseCoeff q m k : ℤ) := by
    exact_mod_cast xi_cq_power_strict_sign_regular_coeff_pos q m k hm hk
  rw [xi_cq_power_strict_sign_regular_signed_entry, ← mul_assoc,
    xi_cq_power_strict_sign_regular_sign_sq]
  simpa using hcoeff

/-- Paper label: `thm:xi-Cq-power-strict-sign-regular`.
The local certificate records the Pascal/reversal base sign law, the positive closed form for the
Fibonacci-binomial power coefficients, and the even/odd sign transfer used by the strict
sign-regularity argument. -/
def paper_xi_cq_power_strict_sign_regular_statement : Prop :=
  (∀ q k : ℕ, k ≤ q →
    0 < xi_cq_power_strict_sign_regular_sign k *
      xi_cq_power_strict_sign_regular_base_entry q k) ∧
  (∀ q m k : ℕ, 0 < m → k ≤ q →
    xiBqPowerEntrywiseCoeff q m k =
      Nat.choose q k * 2 ^ k * xiBqIteratedXCoeff m ^ (q - k) *
        xiBqIteratedYCoeff m ^ k) ∧
  (∀ q m k : ℕ, 0 < m → k ≤ q → 0 < xiBqPowerEntrywiseCoeff q m k) ∧
  (∀ q m k : ℕ, 0 < m → k ≤ q → 0 < xiBqPowerEntrywiseCoeff q (2 * m) k) ∧
  (∀ q m k : ℕ, k ≤ q →
    0 < xi_cq_power_strict_sign_regular_sign k *
      xi_cq_power_strict_sign_regular_signed_entry q (2 * m + 1) k)

theorem paper_xi_cq_power_strict_sign_regular :
    paper_xi_cq_power_strict_sign_regular_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q k hk
    exact xi_cq_power_strict_sign_regular_base_sign q k hk
  · intro q m k _hm _hk
    exact xi_cq_power_strict_sign_regular_coeff_closed_form q m k
  · intro q m k hm hk
    exact xi_cq_power_strict_sign_regular_coeff_pos q m k hm hk
  · intro q m k hm hk
    exact xi_cq_power_strict_sign_regular_coeff_pos q (2 * m) k
      (Nat.mul_pos (by norm_num : 0 < (2 : ℕ)) hm) hk
  · intro q m k hk
    exact xi_cq_power_strict_sign_regular_signed_entry_sign q (2 * m + 1) k
      (Nat.succ_pos (2 * m)) hk

end Omega.Zeta
