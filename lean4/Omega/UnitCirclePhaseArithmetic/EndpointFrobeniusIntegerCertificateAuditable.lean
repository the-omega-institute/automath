import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.SyncKernelWeighted.WittFrobeniusDefectDivisibility

namespace Omega.UnitCirclePhaseArithmetic

open Polynomial

/-- Endpoint specialization of the coefficientwise Witt Frobenius divisibility certificate. -/
theorem paper_endpoint_frobenius_integer_certificate_auditable
    (p k : ℕ) (hp : Nat.Prime p) (hk : 1 ≤ k) (a_pk a_prev : Polynomial ℤ) (σ : ℤ)
    (hσ : σ = -1 ∨ σ = 1)
    (hcoeff :
      ∀ j, ((p ^ k : ℤ) ∣ a_pk.coeff j - if p ∣ j then a_prev.coeff (j / p) else 0)) :
    ((p ^ k : ℤ) ∣ (Omega.SyncKernelWeighted.wittFrobeniusDefect p a_pk a_prev).eval σ) := by
  let _ : σ = -1 ∨ σ = 1 := hσ
  let defect := Omega.SyncKernelWeighted.wittFrobeniusDefect p a_pk a_prev
  have hdefect :
      ∀ j, ((p ^ k : ℤ) ∣ defect.coeff j) :=
    Omega.SyncKernelWeighted.paper_witt_frobenius_defect_divisibility p k hp hk a_pk a_prev hcoeff
  change ((p ^ k : ℤ) ∣ defect.eval σ)
  rw [← Polynomial.sum_C_mul_X_pow_eq defect, Polynomial.eval_sum]
  apply Finset.dvd_sum
  intro j hj
  simpa [Polynomial.eval_mul_X_pow, Polynomial.eval_C] using
    (dvd_mul_of_dvd_left (hdefect j) (σ ^ j))

end Omega.UnitCirclePhaseArithmetic
