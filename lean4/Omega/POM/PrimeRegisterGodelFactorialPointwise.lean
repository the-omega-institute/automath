import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

private theorem pom_prime_register_godel_factorial_pointwise_prod_range_add_two_eq_factorial_succ
    (T : ℕ) : ∏ i ∈ Finset.range T, (i + 2) = Nat.factorial (T + 1) := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      rw [Finset.prod_range_succ, ih]
      simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.factorial_succ (T + 1)).symm

private theorem pom_prime_register_godel_factorial_pointwise_prod_indices (T : ℕ) :
    (∏ i : Fin T, (i.1 + 2)) = Nat.factorial (T + 1) := by
  calc
    (∏ i : Fin T, (i.1 + 2)) = ∏ i ∈ Finset.range T, (i + 2) := by
      simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 2) T)
    _ = Nat.factorial (T + 1) :=
      pom_prime_register_godel_factorial_pointwise_prod_range_add_two_eq_factorial_succ T

/-- Paper label: `cor:pom-prime-register-godel-factorial-pointwise`. Pointwise lower bounds
`a_i ≥ i + 2` force the entire finite product to dominate `(T + 1)!`. -/
theorem paper_pom_prime_register_godel_factorial_pointwise
    (T : ℕ) (a : Fin T → ℕ) (hlb : ∀ i, i.1 + 2 ≤ a i) :
    Nat.factorial (T + 1) ≤ Finset.univ.prod (fun i : Fin T => a i) := by
  calc
    Nat.factorial (T + 1) = ∏ i : Fin T, (i.1 + 2) :=
      pom_prime_register_godel_factorial_pointwise_prod_indices T |>.symm
    _ ≤ ∏ i : Fin T, a i :=
      Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => hlb i)

end Omega.POM
