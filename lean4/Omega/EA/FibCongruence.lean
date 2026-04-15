import Mathlib.Data.Nat.Fib.Basic

namespace Omega.EA

/-- Base congruence value invariant: F_3 = 2·F_2.
    def:fib-congruence (base relation Val side) -/
theorem paper_val_base_e2 : Nat.fib 3 = 2 * Nat.fib 2 := by decide

/-- Recursive congruence value invariant: F_{k+3} = F_{k+2} + F_{k+1}.
    def:fib-congruence (recursive relation Val side) -/
theorem paper_val_recursion_e (k : Nat) :
    Nat.fib (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 1) := by
  rw [show k + 3 = (k + 1) + 2 from by omega, Nat.fib_add_two]
  ring

/-- Value of unit basis vector e_k under Val homomorphism.
    def:val-on-D specialized to single basis vector. -/
def valE (k : Nat) : Nat := Nat.fib (k + 1)

@[simp] theorem valE_one : valE 1 = 1 := by decide

theorem valE_two_eq_two_valE_one : valE 2 = 2 * valE 1 := by decide

theorem valE_recursion (k : Nat) :
    valE (k + 2) = valE (k + 1) + valE k := by
  unfold valE
  rw [show k + 2 + 1 = (k + 1) + 2 from by omega, Nat.fib_add_two]
  ring

/-- Val homomorphism on basis vector equals Fibonacci successor.
    thm:monoid-quotient-is-N (key lemma) -/
theorem paper_val_e_index_eq_fib_succ (k : Nat) :
    valE k = Nat.fib (k + 1) := rfl

/-- Small-value table valE 0..7 = F_1..F_8.
    thm:monoid-quotient-is-N (sanity table) -/
theorem valE_zero_one_two_table :
    valE 0 = 1 ∧ valE 1 = 1 ∧ valE 2 = 2 ∧ valE 3 = 3 ∧
    valE 4 = 5 ∧ valE 5 = 8 ∧ valE 6 = 13 ∧ valE 7 = 21 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- valE is positive for k ≥ 1.
    thm:monoid-quotient-is-N (positivity) -/
theorem valE_pos_of_ge_one {k : Nat} (hk : 1 ≤ k) : 1 ≤ valE k := by
  unfold valE
  exact Nat.fib_pos.mpr (by omega : 0 < k + 1)

/-- valE is monotone.
    thm:monoid-quotient-is-N (monotonicity) -/
theorem valE_mono {j k : Nat} (h : j ≤ k) : valE j ≤ valE k := by
  unfold valE
  exact Nat.fib_mono (by omega : j + 1 ≤ k + 1)

/-- valE is strictly monotone from k ≥ 2.
    thm:monoid-quotient-is-N (strict monotonicity from k ≥ 2) -/
theorem valE_strict_mono_of_ge_two {k : Nat} (hk : 2 ≤ k) :
    valE k < valE (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  -- valE (j+3) = valE (j+2) + valE (j+1), and valE (j+1) ≥ 1
  have hrec : valE (j + 2 + 1) = valE (j + 2) + valE (j + 1) := by
    have := valE_recursion (j + 1)
    simpa [show j + 1 + 2 = j + 2 + 1 from by omega,
           show j + 1 + 1 = j + 2 from by omega] using this
  have hpos : 1 ≤ valE (j + 1) :=
    valE_pos_of_ge_one (by omega : 1 ≤ j + 1)
  omega

/-- R400 milestone package: complete valE specification.
    thm:monoid-quotient-is-N -/
theorem paper_valE_milestone_package :
    valE 1 = 1 ∧
    (∀ k, valE (k + 2) = valE (k + 1) + valE k) ∧
    (valE 0 = 1 ∧ valE 1 = 1 ∧ valE 2 = 2 ∧ valE 3 = 3 ∧
     valE 4 = 5 ∧ valE 5 = 8 ∧ valE 6 = 13 ∧ valE 7 = 21) ∧
    (∀ k : Nat, 1 ≤ k → 1 ≤ valE k) ∧
    (∀ j k : Nat, j ≤ k → valE j ≤ valE k) ∧
    (∀ k : Nat, 2 ≤ k → valE k < valE (k + 1)) ∧
    (∀ k : Nat, valE k = Nat.fib (k + 1)) :=
  ⟨valE_one,
   valE_recursion,
   valE_zero_one_two_table,
   @valE_pos_of_ge_one,
   @valE_mono,
   @valE_strict_mono_of_ge_two,
   paper_val_e_index_eq_fib_succ⟩

end Omega.EA
