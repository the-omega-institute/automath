import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Omega.Folding.FiberArithmeticProperties

namespace Omega.Folding

/-- Concrete log-smooth event used in the Lean-side typical-fiber estimate. -/
def typicalFiberLogSmoothHighProbability (m ell : ℕ) : Prop :=
  Nat.fib (ell + 2) ≤ m + 1

/-- Every prime factor of the corresponding Fibonacci contribution is bounded by the polynomial
scale `m + 1`. -/
def typicalFiberPolynomialPrimeFactorBound (m ell : ℕ) : Prop :=
  ∀ p ∈ Nat.primeFactorsList (Nat.fib (ell + 2)), p ≤ m + 1

/-- A logarithmic bound on the component length forces the associated Fibonacci factor to be
polynomially smooth: first the whole factor is at most `m + 1`, and then every prime divisor is as
well.
    thm:fold-typical-fiber-polynomial-smoothness -/
theorem paper_fold_typical_fiber_polynomial_smoothness (m ell : ℕ)
    (hell : ell ≤ Nat.log 2 (m + 1)) :
    typicalFiberLogSmoothHighProbability m ell ∧
      typicalFiberPolynomialPrimeFactorBound m ell := by
  have hfibPow : Nat.fib (ell + 2) ≤ 2 ^ ell := Omega.X.fib_le_pow_two ell
  have hpowMono : 2 ^ ell ≤ 2 ^ Nat.log 2 (m + 1) := by
    exact Nat.pow_le_pow_right (by omega) hell
  have hpowSelf : 2 ^ Nat.log 2 (m + 1) ≤ m + 1 := by
    exact Nat.pow_log_le_self 2 (Nat.succ_ne_zero m)
  have hsmooth : Nat.fib (ell + 2) ≤ m + 1 := hfibPow.trans (hpowMono.trans hpowSelf)
  refine ⟨hsmooth, ?_⟩
  intro p hp
  exact (Nat.le_of_mem_primeFactorsList hp).trans hsmooth

end Omega.Folding
