import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

open scoped BigOperators

/-- The mixed-prime coordinate kernel: only the diagonal prime blocks are allowed to survive. -/
def primeCoordinateKernel (diag : ℕ → ℤ) (p q : ℕ) : ℤ :=
  if p = q then diag p else 0

/-- The finite product map induced by the coordinate kernel on a prime support set `S`. -/
def primeCoordinateProductMap (S : Finset ℕ) (diag x : ℕ → ℤ) (q : ℕ) : ℤ :=
  Finset.sum S fun p => primeCoordinateKernel diag p q * x p

/-- Paper label: `thm:cdim-star-prime-coordinate-orthogonality`. -/
theorem paper_cdim_star_prime_coordinate_orthogonality
    (S T : Finset ℕ) (diag : ℕ → ℤ) :
    (∀ p, p ∈ S → ∀ q, q ∈ T → p ≠ q → primeCoordinateKernel diag p q = 0) ∧
      ∀ (x : ℕ → ℤ) (q : ℕ), q ∈ T →
        primeCoordinateProductMap S diag x q = if q ∈ S then diag q * x q else 0 := by
  constructor
  · intro p hp q hq hpq
    simp [primeCoordinateKernel, hpq]
  · intro x q hqT
    by_cases hqS : q ∈ S
    · rw [primeCoordinateProductMap, if_pos hqS]
      rw [Finset.sum_eq_single q]
      · simp [primeCoordinateKernel]
      · intro p hp hpq
        simp [primeCoordinateKernel, hpq]
      · intro hqS'
        exact (hqS' hqS).elim
    · rw [primeCoordinateProductMap, if_neg hqS]
      show Finset.sum S (fun p => primeCoordinateKernel diag p q * x p) = (0 : ℤ)
      refine Finset.sum_eq_zero ?_
      intro p hp
      by_cases hpq : p = q
      · subst hpq
        exact (hqS hp).elim
      · simp [primeCoordinateKernel, hpq]

end Omega.CircleDimension
