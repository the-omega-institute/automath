import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic
import Omega.SyncKernelWeighted.WittFrobeniusIteratedDescent

namespace Omega.SyncKernelWeighted

open Polynomial

/-- The Witt Frobenius defect at level `p^k`: subtract the Frobenius-pushed previous stage from
the current stage. -/
noncomputable def wittFrobeniusDefect (p : ℕ) (a_pk a_prev : Polynomial ℤ) : Polynomial ℤ :=
  a_pk - Polynomial.expand ℤ p a_prev

@[simp] lemma coeff_wittFrobeniusDefect (p j : ℕ) (a_pk a_prev : Polynomial ℤ) :
    (wittFrobeniusDefect p a_pk a_prev).coeff j =
      a_pk.coeff j - (Polynomial.expand ℤ p a_prev).coeff j := by
  simp [wittFrobeniusDefect]

/-- The Frobenius congruence modulo `p^k` makes every coefficient of the defect polynomial
divisible by `p^k`.
    prop:witt-frobenius-defect-divisibility -/
theorem paper_witt_frobenius_defect_divisibility
    (p k : ℕ) (hp : Nat.Prime p) (_hk : 1 ≤ k)
    (a_pk a_prev : Polynomial ℤ)
    (hcoeff :
      ∀ j, ((p ^ k : ℤ) ∣ a_pk.coeff j - if p ∣ j then a_prev.coeff (j / p) else 0)) :
    ∀ j, ((p ^ k : ℤ) ∣ (wittFrobeniusDefect p a_pk a_prev).coeff j) := by
  intro j
  simpa [wittFrobeniusDefect, Polynomial.coeff_expand hp.pos, Polynomial.coeff_sub] using hcoeff j

end Omega.SyncKernelWeighted
