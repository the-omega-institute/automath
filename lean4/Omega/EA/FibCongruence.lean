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

end Omega.EA
