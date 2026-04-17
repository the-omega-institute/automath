import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Folding

/-- Integer-valued Fibonacci numbers, used for the low-defect coefficient formulas. -/
def fibZ (n : ℕ) : ℤ :=
  Nat.fib n

private theorem fibZ_add_two (n : ℕ) : fibZ (n + 2) = fibZ (n + 1) + fibZ n := by
  dsimp [fibZ]
  exact_mod_cast Omega.fib_succ_succ' n

private theorem fibZ_linear_closed_form
    (c : ℤ) (offset : ℕ) (a : ℕ → ℤ)
    (hrec : ∀ m, a (m + 2) = a (m + 1) + a m)
    (h0 : a 0 = c * fibZ offset)
    (h1 : a 1 = c * fibZ (offset + 1)) :
    ∀ m, a m = c * fibZ (m + offset) := by
  have hpair : ∀ m, a m = c * fibZ (m + offset) ∧ a (m + 1) = c * fibZ (m + offset + 1) := by
    intro m
    induction m with
    | zero =>
        refine ⟨by simpa [Nat.zero_add] using h0, ?_⟩
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h1
    | succ m ih =>
        rcases ih with ⟨hm, hm1⟩
        refine ⟨by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hm1, ?_⟩
        calc
          a (m + 1 + 1) = a (m + 1) + a m := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrec m
          _ = c * fibZ (m + offset + 1) + c * fibZ (m + offset) := by
            rw [hm1, hm]
          _ = c * fibZ (m + offset + 2) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_add] using
              congrArg (fun z : ℤ => c * z) (fibZ_add_two (m + offset)).symm
          _ = c * fibZ (m + 1 + offset + 1) := by
            congr 2
            omega
  intro m
  exact (hpair m).1

/-- Data extracted from the `p = 1/2` cleared-denominator mismatch recurrence. The low-defect
coefficient rows `k = 0, 1, 2` carry the Fibonacci recurrences and base cases appearing in the
paper's coefficient extraction. -/
structure BernoulliPHalfFibonacciLowDefectShadowData where
  coeff : Fin 3 → ℕ → ℤ
  coeff_zero_recurrence : ∀ m, coeff 0 (m + 2) = coeff 0 (m + 1) + coeff 0 m
  coeff_zero_zero : coeff 0 0 = fibZ 2
  coeff_zero_one : coeff 0 1 = fibZ 3
  coeff_one_recurrence : ∀ m, coeff 1 (m + 4) = coeff 1 (m + 3) + coeff 1 (m + 2)
  coeff_one_zero : coeff 1 0 = 0
  coeff_one_one : coeff 1 1 = 0
  coeff_one_two : coeff 1 2 = fibZ 1
  coeff_one_three : coeff 1 3 = fibZ 2
  coeff_two_recurrence : ∀ m, coeff 2 (m + 5) = coeff 2 (m + 4) + coeff 2 (m + 3)
  coeff_two_zero : coeff 2 0 = 0
  coeff_two_one : coeff 2 1 = 0
  coeff_two_two : coeff 2 2 = 0
  coeff_two_three : coeff 2 3 = 2 * fibZ 2
  coeff_two_four : coeff 2 4 = 2 * fibZ 3

/-- The paper's low-defect Fibonacci shadow formulas for the first three coefficient rows. -/
def BernoulliPHalfFibonacciLowDefectShadowData.low_defect_shadow
    (h : BernoulliPHalfFibonacciLowDefectShadowData) : Prop :=
  (∀ m, h.coeff 0 m = fibZ (m + 2)) ∧
    h.coeff 1 0 = 0 ∧
    h.coeff 1 1 = 0 ∧
    (∀ m, h.coeff 1 (m + 2) = fibZ (m + 1)) ∧
    h.coeff 2 0 = 0 ∧
    h.coeff 2 1 = 0 ∧
    h.coeff 2 2 = 0 ∧
    (∀ m, h.coeff 2 (m + 3) = 2 * fibZ (m + 2))

set_option maxHeartbeats 400000 in
/-- The low-defect Bernoulli-`1/2` mismatch coefficients are Fibonacci shadows:
`a_{m,0} = F_{m+2}`, `a_{m,1} = F_{m-1}` for `m ≥ 2`, and `a_{m,2} = 2 F_{m-1}` for `m ≥ 3`.
    thm:fold-bernoulli-p-fibonacci-low-defect-shadow -/
theorem paper_fold_bernoulli_p_fibonacci_low_defect_shadow
    (h : BernoulliPHalfFibonacciLowDefectShadowData) : h.low_defect_shadow := by
  dsimp [BernoulliPHalfFibonacciLowDefectShadowData.low_defect_shadow]
  have h0 :
      ∀ m, h.coeff 0 m = fibZ (m + 2) := by
    simpa [one_mul] using
      fibZ_linear_closed_form 1 2 (h.coeff 0) h.coeff_zero_recurrence h.coeff_zero_zero
        h.coeff_zero_one
  have h1 :
      ∀ m, h.coeff 1 (m + 2) = fibZ (m + 1) := by
    let a : ℕ → ℤ := fun m => h.coeff 1 (m + 2)
    have hrec : ∀ m, a (m + 2) = a (m + 1) + a m := by
      intro m
      simpa [a, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.coeff_one_recurrence m
    have hbase0 : a 0 = fibZ 1 := by
      simpa [a] using h.coeff_one_two
    have hbase1 : a 1 = fibZ 2 := by
      simpa [a] using h.coeff_one_three
    simpa [a] using fibZ_linear_closed_form 1 1 a hrec hbase0 hbase1
  have h2 :
      ∀ m, h.coeff 2 (m + 3) = 2 * fibZ (m + 2) := by
    let a : ℕ → ℤ := fun m => h.coeff 2 (m + 3)
    have hrec : ∀ m, a (m + 2) = a (m + 1) + a m := by
      intro m
      simpa [a, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.coeff_two_recurrence m
    have hbase0 : a 0 = 2 * fibZ 2 := by
      simpa [a] using h.coeff_two_three
    have hbase1 : a 1 = 2 * fibZ 3 := by
      simpa [a] using h.coeff_two_four
    simpa [a] using fibZ_linear_closed_form 2 2 a hrec hbase0 hbase1
  refine ⟨h0, h.coeff_one_zero, h.coeff_one_one, h1, h.coeff_two_zero, h.coeff_two_one,
    h.coeff_two_two, h2⟩

end Omega.Folding
