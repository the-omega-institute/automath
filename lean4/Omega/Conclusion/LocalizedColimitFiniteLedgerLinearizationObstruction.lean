import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The prime-product witness built from a finite family of exponents. -/
def conclusion_localized_colimit_finite_ledger_linearization_obstruction_prime_product
    {m : ℕ} (primes exponents : Fin m → ℕ) : ℕ :=
  Finset.prod Finset.univ fun i => primes i ^ exponents i

lemma conclusion_localized_colimit_finite_ledger_linearization_obstruction_ledger_pow
    {r : ℕ} (ledger : ℕ → Fin r → ℤ) (h1 : ledger 1 = 0)
    (hmul : ∀ m n, ledger (m * n) = ledger m + ledger n) (a n : ℕ) :
    ledger (a ^ n) = n • ledger a := by
  induction n with
  | zero =>
      simp [h1]
  | succ n ih =>
      rw [pow_succ, hmul, ih, succ_nsmul]

lemma conclusion_localized_colimit_finite_ledger_linearization_obstruction_ledger_finset_prod
    {α : Type*} [DecidableEq α] {r : ℕ} (ledger : ℕ → Fin r → ℤ) (h1 : ledger 1 = 0)
    (hmul : ∀ m n, ledger (m * n) = ledger m + ledger n) (s : Finset α) (f : α → ℕ) :
    ledger (Finset.prod s fun a => f a) = Finset.sum s fun a => ledger (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [h1]
  | @insert a s ha ih =>
      simp [ha, hmul, ih]

lemma conclusion_localized_colimit_finite_ledger_linearization_obstruction_ledger_prime_product
    {m r : ℕ} (ledger : ℕ → Fin r → ℤ) (h1 : ledger 1 = 0)
    (hmul : ∀ m n, ledger (m * n) = ledger m + ledger n) (primes exponents : Fin m → ℕ) :
    ledger
        (conclusion_localized_colimit_finite_ledger_linearization_obstruction_prime_product
          primes exponents) =
      ∑ i, exponents i • ledger (primes i) := by
  classical
  unfold conclusion_localized_colimit_finite_ledger_linearization_obstruction_prime_product
  calc
    ledger (Finset.prod Finset.univ fun i => primes i ^ exponents i) =
        Finset.sum Finset.univ fun i => ledger (primes i ^ exponents i) := by
      exact
        conclusion_localized_colimit_finite_ledger_linearization_obstruction_ledger_finset_prod
          ledger h1 hmul Finset.univ (fun i => primes i ^ exponents i)
    _ = Finset.sum Finset.univ fun i => exponents i • ledger (primes i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [conclusion_localized_colimit_finite_ledger_linearization_obstruction_ledger_pow,
        h1, hmul]

/-- Paper label: `thm:conclusion-localized-colimit-finite-ledger-linearization-obstruction`. An
explicit integer relation among the prime images forces the two corresponding prime products to
have the same ledger value, so any such finite-rank additive ledger is noninjective once the two
products are genuinely distinct. -/
theorem paper_conclusion_localized_colimit_finite_ledger_linearization_obstruction
    {r : ℕ} (ledger : ℕ → Fin r → ℤ) (h1 : ledger 1 = 0)
    (hmul : ∀ m n, ledger (m * n) = ledger m + ledger n) (primes : Fin (r + 1) → ℕ)
    (positive negative : Fin (r + 1) → ℕ)
    (hrelation :
      Finset.sum Finset.univ (fun i => positive i • ledger (primes i)) =
        Finset.sum Finset.univ (fun i => negative i • ledger (primes i)))
    (hneq :
      conclusion_localized_colimit_finite_ledger_linearization_obstruction_prime_product
          primes positive ≠
        conclusion_localized_colimit_finite_ledger_linearization_obstruction_prime_product
          primes negative) :
    ¬ Function.Injective ledger := by
  intro hinj
  have himages :
      ledger
          (conclusion_localized_colimit_finite_ledger_linearization_obstruction_prime_product
            primes positive) =
        ledger
          (conclusion_localized_colimit_finite_ledger_linearization_obstruction_prime_product
            primes negative) := by
    rw [conclusion_localized_colimit_finite_ledger_linearization_obstruction_ledger_prime_product
        ledger h1 hmul primes positive,
      conclusion_localized_colimit_finite_ledger_linearization_obstruction_ledger_prime_product
        ledger h1 hmul primes negative,
      hrelation]
  exact hneq (hinj himages)

end Omega.Conclusion
