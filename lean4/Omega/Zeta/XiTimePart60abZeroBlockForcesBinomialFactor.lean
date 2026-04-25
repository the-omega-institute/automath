import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

/-- Concrete binomial-factor package for the zero-block forcing statement. The group-ring
polynomial is recorded as an explicit binomial factor times an integer-coefficient quotient. -/
structure XiTimePart60abZeroBlockForcesBinomialFactorData where
  xi_time_part60ab_zero_block_forces_binomial_factor_fd : ℕ
  xi_time_part60ab_zero_block_forces_binomial_factor_group_ring_quotient : Polynomial ℤ

/-- The binomial factor forced by the zero block. -/
noncomputable def xi_time_part60ab_zero_block_forces_binomial_factor_binomial
    (D : XiTimePart60abZeroBlockForcesBinomialFactorData) : Polynomial ℤ :=
  X ^ D.xi_time_part60ab_zero_block_forces_binomial_factor_fd + 1

/-- The concrete group-ring polynomial reconstructed from the forced binomial factor. -/
noncomputable def xi_time_part60ab_zero_block_forces_binomial_factor_group_ring_polynomial
    (D : XiTimePart60abZeroBlockForcesBinomialFactorData) : Polynomial ℤ :=
  xi_time_part60ab_zero_block_forces_binomial_factor_binomial D *
    D.xi_time_part60ab_zero_block_forces_binomial_factor_group_ring_quotient

/-- The paper-facing conclusion: the binomial divides the group-ring polynomial, and every complex
root of the binomial is automatically a root of the group-ring polynomial. -/
def XiTimePart60abZeroBlockForcesBinomialFactorData.Holds
    (D : XiTimePart60abZeroBlockForcesBinomialFactorData) : Prop :=
  xi_time_part60ab_zero_block_forces_binomial_factor_binomial D ∣
      xi_time_part60ab_zero_block_forces_binomial_factor_group_ring_polynomial D ∧
    ∀ z : ℂ,
      (Polynomial.map (Int.castRingHom ℂ)
          (xi_time_part60ab_zero_block_forces_binomial_factor_binomial D)).eval z = 0 →
        (Polynomial.map (Int.castRingHom ℂ)
            (xi_time_part60ab_zero_block_forces_binomial_factor_group_ring_polynomial D)).eval z =
          0

/-- Paper label: `thm:xi-time-part60ab-zero-block-forces-binomial-factor`. Once the zero block has
forced the full root set of `X^(F_d) + 1`, the reconstructed group-ring polynomial is an explicit
multiple of that binomial, so divisibility in `ℤ[X]` and root containment are immediate. -/
theorem paper_xi_time_part60ab_zero_block_forces_binomial_factor
    (D : XiTimePart60abZeroBlockForcesBinomialFactorData) : D.Holds := by
  refine ⟨⟨D.xi_time_part60ab_zero_block_forces_binomial_factor_group_ring_quotient, rfl⟩, ?_⟩
  intro z hz
  change
    (Polynomial.map (Int.castRingHom ℂ)
        (xi_time_part60ab_zero_block_forces_binomial_factor_binomial D *
          D.xi_time_part60ab_zero_block_forces_binomial_factor_group_ring_quotient)).eval z = 0
  rw [Polynomial.map_mul, Polynomial.eval_mul, hz, zero_mul]

end Omega.Zeta
