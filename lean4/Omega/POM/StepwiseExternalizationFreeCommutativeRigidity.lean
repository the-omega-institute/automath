import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.POM

open scoped BigOperators

abbrev pom_stepwise_externalization_free_commutative_rigidity_data := ℕ

noncomputable def pom_stepwise_externalization_free_commutative_rigidity_generator
    (D : pom_stepwise_externalization_free_commutative_rigidity_data) (i : Fin D) : Fin D →₀ ℕ :=
  Finsupp.single i 1

noncomputable def pom_stepwise_externalization_free_commutative_rigidity_encoding
    (D : pom_stepwise_externalization_free_commutative_rigidity_data) (v : Fin D →₀ ℕ) : ℕ :=
  v.support.prod fun i => (Omega.POM.nthPrime i.1) ^ v i

def pom_stepwise_externalization_free_commutative_rigidity_stmt
    (D : pom_stepwise_externalization_free_commutative_rigidity_data) : Prop :=
  (∀ i : Fin D,
      pom_stepwise_externalization_free_commutative_rigidity_encoding D
          (pom_stepwise_externalization_free_commutative_rigidity_generator D i) =
        Omega.POM.nthPrime i.1) ∧
    Function.Injective
      (fun i : Fin D =>
        pom_stepwise_externalization_free_commutative_rigidity_encoding D
          (pom_stepwise_externalization_free_commutative_rigidity_generator D i)) ∧
    Pairwise fun i j : Fin D =>
      Nat.Coprime
        (pom_stepwise_externalization_free_commutative_rigidity_encoding D
          (pom_stepwise_externalization_free_commutative_rigidity_generator D i))
        (pom_stepwise_externalization_free_commutative_rigidity_encoding D
          (pom_stepwise_externalization_free_commutative_rigidity_generator D j))

/-- Paper label: `thm:pom-stepwise-externalization-free-commutative-rigidity`. Fixing the prime
enumeration `nthPrime` makes the singleton generators of the free commutative monoid land on
pairwise coprime prime coordinates, so the chosen generators already embed injectively into the
prime-register axis. -/
theorem paper_pom_stepwise_externalization_free_commutative_rigidity
    (D : pom_stepwise_externalization_free_commutative_rigidity_data) :
    pom_stepwise_externalization_free_commutative_rigidity_stmt D := by
  have hgen :
      ∀ i : Fin D,
        pom_stepwise_externalization_free_commutative_rigidity_encoding D
            (pom_stepwise_externalization_free_commutative_rigidity_generator D i) =
          Omega.POM.nthPrime i.1 := by
    intro i
    rw [pom_stepwise_externalization_free_commutative_rigidity_encoding,
      pom_stepwise_externalization_free_commutative_rigidity_generator,
      Finsupp.support_single_ne_zero]
    · simp
    · norm_num
  refine ⟨hgen, ?_, ?_⟩
  · intro i j hij
    have hij' : Omega.POM.nthPrime i.1 = Omega.POM.nthPrime j.1 := by
      simpa [hgen i, hgen j] using hij
    exact Fin.ext ((Nat.nth_strictMono Nat.infinite_setOf_prime).injective hij')
  · intro i j hij
    have hneq : Omega.POM.nthPrime i.1 ≠ Omega.POM.nthPrime j.1 := by
      intro hEq
      apply hij
      exact Fin.ext ((Nat.nth_strictMono Nat.infinite_setOf_prime).injective hEq)
    have hprime_i : Nat.Prime (Omega.POM.nthPrime i.1) := Omega.POM.nthPrime_prime i.1
    have hprime_j : Nat.Prime (Omega.POM.nthPrime j.1) := Omega.POM.nthPrime_prime j.1
    simpa [hgen i, hgen j] using
      (Nat.coprime_primes hprime_i hprime_j).2 hneq

end Omega.POM
