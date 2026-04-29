import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

namespace Omega.Zeta

/-- The Frobenius certificate type used by the sextic specialization audit. -/
inductive xi_j_sextic_two_primes_force_s6_frobenius_certificate where
  | six_cycle
  | transposition
deriving DecidableEq, Fintype

/-- The concrete `6`-cycle on the six roots. -/
def xi_j_sextic_two_primes_force_s6_cycle : Equiv.Perm (Fin 6) :=
  finRotate 6

/-- The adjacent transposition forced by the `(2)(1)(1)(1)(1)` factorization. -/
def xi_j_sextic_two_primes_force_s6_transposition : Equiv.Perm (Fin 6) :=
  Equiv.swap (0 : Fin 6) 1

/-- Concrete data for the two-prime sextic Galois certificate. The two finite fields record the
Dedekind factorization witnesses, while the subgroup fields record their Frobenius permutations. -/
structure xi_j_sextic_two_primes_force_s6_data where
  xi_j_sextic_two_primes_force_s6_galois_group : Subgroup (Equiv.Perm (Fin 6))
  xi_j_sextic_two_primes_force_s6_first_prime : ℕ
  xi_j_sextic_two_primes_force_s6_second_prime : ℕ
  xi_j_sextic_two_primes_force_s6_first_certificate :
    xi_j_sextic_two_primes_force_s6_frobenius_certificate
  xi_j_sextic_two_primes_force_s6_second_certificate :
    xi_j_sextic_two_primes_force_s6_frobenius_certificate
  xi_j_sextic_two_primes_force_s6_primes_distinct :
    xi_j_sextic_two_primes_force_s6_first_prime ≠
      xi_j_sextic_two_primes_force_s6_second_prime
  xi_j_sextic_two_primes_force_s6_first_certificate_eq :
    xi_j_sextic_two_primes_force_s6_first_certificate =
      xi_j_sextic_two_primes_force_s6_frobenius_certificate.six_cycle
  xi_j_sextic_two_primes_force_s6_second_certificate_eq :
    xi_j_sextic_two_primes_force_s6_second_certificate =
      xi_j_sextic_two_primes_force_s6_frobenius_certificate.transposition
  xi_j_sextic_two_primes_force_s6_cycle_mem :
    xi_j_sextic_two_primes_force_s6_cycle ∈ xi_j_sextic_two_primes_force_s6_galois_group
  xi_j_sextic_two_primes_force_s6_transposition_mem :
    xi_j_sextic_two_primes_force_s6_transposition ∈
      xi_j_sextic_two_primes_force_s6_galois_group

namespace xi_j_sextic_two_primes_force_s6_data

/-- The Galois group is the full symmetric group in degree six. -/
def xi_j_sextic_two_primes_force_s6_galois_group_is_s6
    (D : xi_j_sextic_two_primes_force_s6_data) : Prop :=
  D.xi_j_sextic_two_primes_force_s6_galois_group = ⊤

end xi_j_sextic_two_primes_force_s6_data

open xi_j_sextic_two_primes_force_s6_data

lemma xi_j_sextic_two_primes_force_s6_transposition_eq_adjacent :
    xi_j_sextic_two_primes_force_s6_transposition =
      Equiv.swap (0 : Fin 6) (xi_j_sextic_two_primes_force_s6_cycle 0) := by
  ext x
  fin_cases x <;> native_decide

lemma xi_j_sextic_two_primes_force_s6_cycle_transposition_closure :
    Subgroup.closure
        ({xi_j_sextic_two_primes_force_s6_cycle,
          xi_j_sextic_two_primes_force_s6_transposition} :
          Set (Equiv.Perm (Fin 6))) =
      ⊤ := by
  rw [xi_j_sextic_two_primes_force_s6_transposition_eq_adjacent]
  exact Equiv.Perm.closure_cycle_adjacent_swap
    (isCycle_finRotate_of_le (n := 6) (by norm_num))
    (support_finRotate_of_le (n := 6) (by norm_num))
    (0 : Fin 6)

/-- Paper label: `prop:xi-j-sextic-two-primes-force-s6`. -/
theorem paper_xi_j_sextic_two_primes_force_s6
    (D : xi_j_sextic_two_primes_force_s6_data) :
    D.xi_j_sextic_two_primes_force_s6_galois_group_is_s6 := by
  unfold xi_j_sextic_two_primes_force_s6_galois_group_is_s6
  have hclosure_le :
      Subgroup.closure
          ({xi_j_sextic_two_primes_force_s6_cycle,
            xi_j_sextic_two_primes_force_s6_transposition} :
            Set (Equiv.Perm (Fin 6))) ≤
        D.xi_j_sextic_two_primes_force_s6_galois_group := by
    refine (Subgroup.closure_le D.xi_j_sextic_two_primes_force_s6_galois_group).2 ?_
    intro σ hσ
    rcases hσ with hσ | hσ
    · simpa [hσ] using D.xi_j_sextic_two_primes_force_s6_cycle_mem
    · rw [Set.mem_singleton_iff] at hσ
      simpa [hσ] using D.xi_j_sextic_two_primes_force_s6_transposition_mem
  rw [xi_j_sextic_two_primes_force_s6_cycle_transposition_closure] at hclosure_le
  exact top_unique hclosure_le

end Omega.Zeta
