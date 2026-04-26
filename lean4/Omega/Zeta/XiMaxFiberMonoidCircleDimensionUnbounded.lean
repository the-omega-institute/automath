import Mathlib.Tactic
import Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension
import Omega.Zeta.MinimalAuditChainPrimeSupport

namespace Omega.Zeta

open Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

/-- Concrete max-fiber multiplicity model used for the monoid audit chain. -/
def xi_max_fiber_monoid_circle_dimension_unbounded_maxFiberMultiplicity (m : ℕ) : ℕ :=
  minimalAuditChainLcm m

/-- Circle dimension of the rank-`N` finite prime-support model. -/
def xi_max_fiber_monoid_circle_dimension_unbounded_circleDimension (N : ℕ) : ℚ :=
  homHalfCircleDim N

/-- Concrete package for `thm:xi-max-fiber-monoid-circle-dimension-unbounded`. -/
def xi_max_fiber_monoid_circle_dimension_unbounded_statement : Prop :=
  (∀ B : ℕ, ∃ N : ℕ,
    (B : ℚ) ≤ xi_max_fiber_monoid_circle_dimension_unbounded_circleDimension N) ∧
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ p : ℕ,
      Nat.Prime p ∧
        p ∣ xi_max_fiber_monoid_circle_dimension_unbounded_maxFiberMultiplicity k ∧
        ¬ p ∣ xi_max_fiber_monoid_circle_dimension_unbounded_maxFiberMultiplicity (k - 1)

lemma xi_max_fiber_monoid_circle_dimension_unbounded_cdim_unbounded :
    ∀ B : ℕ, ∃ N : ℕ,
      (B : ℚ) ≤ xi_max_fiber_monoid_circle_dimension_unbounded_circleDimension N := by
  intro B
  refine ⟨2 * B, ?_⟩
  have hdim :
      xi_max_fiber_monoid_circle_dimension_unbounded_circleDimension (2 * B) =
        ((2 * B : ℕ) : ℚ) / 2 := by
    exact (paper_xi_finite_prime_support_multiplicative_half_circle_dimension (2 * B)).1
  rw [hdim]
  norm_num

lemma xi_max_fiber_monoid_circle_dimension_unbounded_fresh_primes :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ p : ℕ,
      Nat.Prime p ∧
        p ∣ xi_max_fiber_monoid_circle_dimension_unbounded_maxFiberMultiplicity k ∧
        ¬ p ∣ xi_max_fiber_monoid_circle_dimension_unbounded_maxFiberMultiplicity (k - 1) := by
  simpa [xi_max_fiber_monoid_circle_dimension_unbounded_maxFiberMultiplicity] using
    paper_xi_primitive_prime_divisor_forces_unbounded_prime_support

/-- Paper label: `thm:xi-max-fiber-monoid-circle-dimension-unbounded`. -/
theorem paper_xi_max_fiber_monoid_circle_dimension_unbounded :
    xi_max_fiber_monoid_circle_dimension_unbounded_statement := by
  exact ⟨xi_max_fiber_monoid_circle_dimension_unbounded_cdim_unbounded,
    xi_max_fiber_monoid_circle_dimension_unbounded_fresh_primes⟩

end Omega.Zeta
