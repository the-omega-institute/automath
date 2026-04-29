import Mathlib.Tactic

namespace Omega.SyncKernelWeighted.WittPkSparsification

/-- Paper seed: coefficientwise `p^k`-sparsification under a Frobenius pushforward congruence.
    prop:witt-pk-sparsification -/
theorem paper_witt_pk_sparsification_seeds
    (p k : ℕ) (hp : Nat.Prime p) (_hk : 1 ≤ k)
    (a_pk a_prev : ℕ → ℤ)
    (hcoeff : ∀ j, ((p ^ k : ℤ) ∣ a_pk j - if p ∣ j then a_prev (j / p) else 0)) :
    (∀ j, ¬ p ∣ j → ((p ^ k : ℤ) ∣ a_pk j)) ∧
    (∀ l, ((p ^ k : ℤ) ∣ a_pk (p * l) - a_prev l)) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    simpa [hj] using hcoeff j
  · intro l
    have hdiv : p ∣ p * l := dvd_mul_right p l
    simpa [hdiv, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_div_right _ hp.pos] using
      hcoeff (p * l)

/-- Packaged form of the `p^k`-sparsification seeds.
    prop:witt-pk-sparsification -/
theorem paper_witt_pk_sparsification_package
    (p k : ℕ) (hp : Nat.Prime p) (hk : 1 ≤ k)
    (a_pk a_prev : ℕ → ℤ)
    (hcoeff : ∀ j, ((p ^ k : ℤ) ∣ a_pk j - if p ∣ j then a_prev (j / p) else 0)) :
    (∀ j, ¬ p ∣ j → ((p ^ k : ℤ) ∣ a_pk j)) ∧
    (∀ l, ((p ^ k : ℤ) ∣ a_pk (p * l) - a_prev l)) :=
  paper_witt_pk_sparsification_seeds p k hp hk a_pk a_prev hcoeff

/-- Exact paper-named wrapper for coefficientwise `p^k`-sparsification.
    prop:witt-pk-sparsification -/
theorem paper_witt_pk_sparsification
    (p k : ℕ) (hp : Nat.Prime p) (hk : 1 ≤ k)
    (a_pk a_prev : ℕ → ℤ)
    (hcoeff : ∀ j, ((p ^ k : ℤ) ∣ a_pk j - if p ∣ j then a_prev (j / p) else 0)) :
    (∀ j, ¬ p ∣ j → ((p ^ k : ℤ) ∣ a_pk j)) ∧
    (∀ l, ((p ^ k : ℤ) ∣ a_pk (p * l) - a_prev l)) :=
  paper_witt_pk_sparsification_package p k hp hk a_pk a_prev hcoeff

end Omega.SyncKernelWeighted.WittPkSparsification
