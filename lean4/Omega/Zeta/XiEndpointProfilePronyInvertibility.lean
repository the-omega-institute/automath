import Omega.Zeta.XiEndpointProfileCfiniteHankelRank

namespace Omega.Zeta

open scoped BigOperators

/-- The first `4N` Taylor coefficients used by the Prony reconstruction window. -/
def xi_endpoint_profile_prony_invertibility_first_window
    {N : ℕ} (γ δ : Fin N → ℚ) : Fin (4 * N) → ℚ :=
  fun n => xi_endpoint_profile_cfinite_hankel_rank_coeff γ δ n

/-- The endpoint parameter pair attached to one quadratic pole factor. -/
def xi_endpoint_profile_prony_invertibility_pair
    {N : ℕ} (γ δ : Fin N → ℚ) (k : Fin N) : ℚ × ℚ :=
  (γ k, δ k)

/-- Equality of endpoint parameter pairs up to the natural conjugation ambiguity `γ ↦ -γ`. -/
def xi_endpoint_profile_prony_invertibility_pair_equiv (u v : ℚ × ℚ) : Prop :=
  u.2 = v.2 ∧ (u.1 = v.1 ∨ u.1 = -v.1)

/-- Concrete proposition encoding the paper's `4N`-coefficient Prony invertibility package. -/
def xi_endpoint_profile_prony_invertibility_statement
    (N : ℕ) (γ δ : Fin N → ℚ) : Prop :=
  (∀ n : Fin (4 * N),
      xi_endpoint_profile_prony_invertibility_first_window γ δ n =
        xi_endpoint_profile_cfinite_hankel_rank_coeff γ δ n) ∧
    (∀ q : ℚ,
      xi_endpoint_profile_cfinite_hankel_rank_denominator γ δ q =
        ∏ k, xi_endpoint_profile_cfinite_hankel_rank_quadratic_factor γ δ k q) ∧
    (∀ q : ℚ,
      xi_endpoint_profile_cfinite_hankel_rank_generating_series γ δ q =
        1 / xi_endpoint_profile_cfinite_hankel_rank_denominator γ δ q) ∧
    xi_endpoint_profile_cfinite_hankel_rank_minimal_order N = 2 * N ∧
    xi_endpoint_profile_cfinite_hankel_rank_hankel_rank N = 2 * N ∧
    (∃ recoveredDenominator : ℚ → ℚ,
      (∀ q : ℚ,
        recoveredDenominator q = xi_endpoint_profile_cfinite_hankel_rank_denominator γ δ q) ∧
      (∀ γ' δ' : Fin N → ℚ,
        (∀ n : Fin (4 * N),
          xi_endpoint_profile_cfinite_hankel_rank_coeff γ' δ' n =
            xi_endpoint_profile_prony_invertibility_first_window γ δ n) →
        xi_endpoint_profile_cfinite_hankel_rank_denominator γ' δ' = recoveredDenominator) ∧
      (∀ γ' δ' : Fin N → ℚ,
        xi_endpoint_profile_cfinite_hankel_rank_denominator γ' δ' = recoveredDenominator →
        ∃ σ : Equiv.Perm (Fin N),
          ∀ k : Fin N,
            xi_endpoint_profile_prony_invertibility_pair_equiv
              (xi_endpoint_profile_prony_invertibility_pair γ' δ' (σ k))
              (xi_endpoint_profile_prony_invertibility_pair γ δ k)))

/-- Paper label: `cor:xi-endpoint-profile-prony-invertibility`. -/
def paper_xi_endpoint_profile_prony_invertibility (N : ℕ) (γ δ : Fin N → ℚ) : Prop :=
  xi_endpoint_profile_prony_invertibility_statement N γ δ

end Omega.Zeta
