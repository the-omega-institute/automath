import Mathlib

namespace Omega.POM

open Finset
open scoped BigOperators

/-- The `t`-th complete-homogeneous recurrence step determined by the elementary coefficients
`e₁, …, e_{t+1}`. -/
def completeHomogeneousRecurrence (e h : Nat → ℚ) (t : Nat) : ℚ :=
  Finset.sum (range (t + 1)) fun j => (-1 : ℚ) ^ j * e (j + 1) * h (t - j)

/-- Two elementary-coefficient sequences that generate the same complete-homogeneous curve agree
on the observed prefix. This is the upper-triangular uniqueness step behind recovering the weight
multiset from the homogeneous curve. -/
theorem paper_pom_invert_w_from_homogeneous_curve
    (n : Nat) (h e e' : Nat → ℚ) (h0 : h 0 = 1) (he0 : e 0 = 1) (he0' : e' 0 = 1)
    (hrec : ∀ t < n, h (t + 1) = completeHomogeneousRecurrence e h t)
    (hrec' : ∀ t < n, h (t + 1) = completeHomogeneousRecurrence e' h t) :
    ∀ t ≤ n, e t = e' t := by
  intro t ht
  induction' t using Nat.strong_induction_on with t ih
  cases t with
  | zero =>
      simp [he0, he0']
  | succ s =>
      have hs : s < n := Nat.lt_of_succ_le ht
      have hmain : completeHomogeneousRecurrence e h s = completeHomogeneousRecurrence e' h s := by
        rw [← hrec s hs, hrec' s hs]
      have hsum :
          Finset.sum (range s) (fun j => (-1 : ℚ) ^ j * e (j + 1) * h (s - j)) =
            Finset.sum (range s) (fun j => (-1 : ℚ) ^ j * e' (j + 1) * h (s - j)) := by
        refine sum_congr rfl ?_
        intro j hj
        have hij : e (j + 1) = e' (j + 1) := by
          apply ih (j + 1)
          · exact Nat.succ_lt_succ (mem_range.mp hj)
          · exact le_trans (Nat.succ_le_of_lt (Nat.lt_succ_of_lt (mem_range.mp hj))) ht
        rw [hij]
      rw [completeHomogeneousRecurrence, completeHomogeneousRecurrence, sum_range_succ,
        sum_range_succ] at hmain
      rw [hsum] at hmain
      have hcoeff :
          (-1 : ℚ) ^ s * e (s + 1) * h (s - s) = (-1 : ℚ) ^ s * e' (s + 1) * h (s - s) := by
        exact add_left_cancel hmain
      have hcoeff' : (-1 : ℚ) ^ s * e (s + 1) = (-1 : ℚ) ^ s * e' (s + 1) := by
        simpa [Nat.sub_self, h0] using hcoeff
      exact mul_left_cancel₀ (pow_ne_zero s (by norm_num)) hcoeff'

end Omega.POM
