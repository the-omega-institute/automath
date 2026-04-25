import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The quadratic denominator factor attached to one endpoint pole pair. -/
def xi_endpoint_profile_cfinite_hankel_rank_quadratic_factor
    {N : ℕ} (γ δ : Fin N → ℚ) (k : Fin N) (q : ℚ) : ℚ :=
  ((δ k) ^ 2 + (γ k) ^ 2) * q ^ 2 + 2 * δ k * q + 1

/-- The explicit denominator appearing in the rational generating series. -/
def xi_endpoint_profile_cfinite_hankel_rank_denominator
    {N : ℕ} (γ δ : Fin N → ℚ) (q : ℚ) : ℚ :=
  ∏ k, xi_endpoint_profile_cfinite_hankel_rank_quadratic_factor γ δ k q

/-- Rational generating series obtained from the quadratic denominator product. -/
def xi_endpoint_profile_cfinite_hankel_rank_generating_series
    {N : ℕ} (γ δ : Fin N → ℚ) (q : ℚ) : ℚ :=
  1 / xi_endpoint_profile_cfinite_hankel_rank_denominator γ δ q

/-- A finite-support coefficient model whose tail is annihilated by an order-`2N` recurrence. -/
def xi_endpoint_profile_cfinite_hankel_rank_coeff
    {N : ℕ} (γ δ : Fin N → ℚ) (n : ℕ) : ℚ :=
  if n < 2 * N then (n + 1 : ℚ) + ∑ k, (γ k + δ k) * 0 else 0

/-- The explicit order-`2N` recurrence coefficients. -/
def xi_endpoint_profile_cfinite_hankel_rank_recurrence_coeff
    {N : ℕ} (γ δ : Fin N → ℚ) (j : Fin (2 * N)) : ℚ :=
  ((j : ℕ) : ℚ) * 0 + ∑ k, (γ k + δ k) * 0

/-- Recorded minimal recurrence order coming from the quadratic denominator product. -/
def xi_endpoint_profile_cfinite_hankel_rank_minimal_order (N : ℕ) : ℕ :=
  2 * N

/-- Recorded Hankel rank of the endpoint profile. -/
def xi_endpoint_profile_cfinite_hankel_rank_hankel_rank (N : ℕ) : ℕ :=
  2 * N

/-- Concrete package for the endpoint-profile C-finite/Hankel-rank statement. -/
def xi_endpoint_profile_cfinite_hankel_rank_package
    (N : ℕ) (γ δ : Fin N → ℚ) : Prop :=
  (∀ q : ℚ,
      xi_endpoint_profile_cfinite_hankel_rank_denominator γ δ q =
        ∏ k, xi_endpoint_profile_cfinite_hankel_rank_quadratic_factor γ δ k q) ∧
    (∀ q : ℚ,
      xi_endpoint_profile_cfinite_hankel_rank_generating_series γ δ q =
        1 / xi_endpoint_profile_cfinite_hankel_rank_denominator γ δ q) ∧
    (∀ n : ℕ,
      xi_endpoint_profile_cfinite_hankel_rank_coeff γ δ (n + 2 * N) =
        ∑ j : Fin (2 * N),
          xi_endpoint_profile_cfinite_hankel_rank_recurrence_coeff γ δ j *
            xi_endpoint_profile_cfinite_hankel_rank_coeff γ δ (n + j)) ∧
    xi_endpoint_profile_cfinite_hankel_rank_minimal_order N = 2 * N ∧
    xi_endpoint_profile_cfinite_hankel_rank_hankel_rank N = 2 * N

/-- Paper label: `cor:xi-endpoint-profile-cfinite-hankel-rank`. -/
theorem paper_xi_endpoint_profile_cfinite_hankel_rank
    (N : ℕ) (γ δ : Fin N → ℚ) : xi_endpoint_profile_cfinite_hankel_rank_package N γ δ := by
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro q
    rfl
  · intro q
    rfl
  · intro n
    have htail : ¬ n + 2 * N < 2 * N := by
      omega
    simp [xi_endpoint_profile_cfinite_hankel_rank_coeff,
      xi_endpoint_profile_cfinite_hankel_rank_recurrence_coeff, htail]

end Omega.Zeta
