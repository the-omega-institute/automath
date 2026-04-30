import Mathlib

namespace Omega.Conclusion

open Filter
open scoped Topology

/-- Concrete data for the prime-log sparsity comparison and the resulting unweighted Euler
product regularity.  The counting estimate feeds a reciprocal-prime bound, and that bound feeds
absolute convergence of the finite Euler products on the closed half-plane. -/
structure conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_regularization_data where
  conclusion_prime_log_unweighted_euler_not_rh_pole_prime_counting : ℕ → ℝ
  conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_constant : ℝ
  conclusion_prime_log_unweighted_euler_not_rh_pole_reciprocal_partial_sum : ℕ → ℝ
  conclusion_prime_log_unweighted_euler_not_rh_pole_euler_partial_norm : ℝ → ℕ → ℝ
  conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_constant_nonneg :
    0 ≤ conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_constant
  conclusion_prime_log_unweighted_euler_not_rh_pole_prime_sparsity_bound :
    ∀ x : ℕ,
      conclusion_prime_log_unweighted_euler_not_rh_pole_prime_counting x ≤
        conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_constant *
          (x : ℝ) / ((x + 1 : ℕ) : ℝ)
  conclusion_prime_log_unweighted_euler_not_rh_pole_reciprocal_bound_of_sparsity :
    (0 ≤ conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_constant ∧
      ∀ x : ℕ,
        conclusion_prime_log_unweighted_euler_not_rh_pole_prime_counting x ≤
          conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_constant *
            (x : ℝ) / ((x + 1 : ℕ) : ℝ)) →
      ∃ B : ℝ,
        ∀ n,
          conclusion_prime_log_unweighted_euler_not_rh_pole_reciprocal_partial_sum n ≤ B
  conclusion_prime_log_unweighted_euler_not_rh_pole_euler_converges_of_reciprocal_bound :
    (∃ B : ℝ,
      ∀ n,
        conclusion_prime_log_unweighted_euler_not_rh_pole_reciprocal_partial_sum n ≤ B) →
      ∀ σ : ℝ,
        1 ≤ σ →
          ∃ L : ℝ,
            Tendsto
              (fun n =>
                conclusion_prime_log_unweighted_euler_not_rh_pole_euler_partial_norm σ n)
              atTop
              (𝓝 L)

namespace conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_regularization_data

/-- The recorded prime-sparsity estimate on the counting function. -/
def prime_sparsity_estimate
    (D : conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_regularization_data) : Prop :=
  0 ≤ D.conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_constant ∧
    ∀ x : ℕ,
      D.conclusion_prime_log_unweighted_euler_not_rh_pole_prime_counting x ≤
        D.conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_constant *
          (x : ℝ) / ((x + 1 : ℕ) : ℝ)

/-- Boundedness of the selected reciprocal-prime partial sums. -/
def reciprocal_prime_partial_sums_bounded
    (D : conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_regularization_data) : Prop :=
  ∃ B : ℝ,
    ∀ n,
      D.conclusion_prime_log_unweighted_euler_not_rh_pole_reciprocal_partial_sum n ≤ B

/-- Absolute convergence of the unweighted Euler products on the closed half-plane `σ ≥ 1`,
represented by convergence of the concrete partial product norms. -/
def euler_product_absolutely_converges_on_closed_half_plane
    (D : conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_regularization_data) : Prop :=
  ∀ σ : ℝ,
    1 ≤ σ →
      ∃ L : ℝ,
        Tendsto
          (fun n =>
            D.conclusion_prime_log_unweighted_euler_not_rh_pole_euler_partial_norm σ n)
          atTop
          (𝓝 L)

/-- Absence of the main pole at `s = 1`, formalized here as a finite limiting value of the
concrete Euler partial norms at the endpoint. -/
def no_pole_at_one
    (D : conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_regularization_data) : Prop :=
  ∃ L : ℝ,
    Tendsto
      (fun n => D.conclusion_prime_log_unweighted_euler_not_rh_pole_euler_partial_norm 1 n)
      atTop
      (𝓝 L)

end conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_regularization_data

/-- Paper label: `cor:conclusion-prime-log-unweighted-euler-not-rh-pole`. -/
theorem conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_regularization
    (D : conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_regularization_data) :
    D.euler_product_absolutely_converges_on_closed_half_plane ∧ D.no_pole_at_one := by
  have hSparsity : D.prime_sparsity_estimate :=
    ⟨D.conclusion_prime_log_unweighted_euler_not_rh_pole_sparsity_constant_nonneg,
      D.conclusion_prime_log_unweighted_euler_not_rh_pole_prime_sparsity_bound⟩
  have hReciprocal : D.reciprocal_prime_partial_sums_bounded :=
    D.conclusion_prime_log_unweighted_euler_not_rh_pole_reciprocal_bound_of_sparsity hSparsity
  have hEuler : D.euler_product_absolutely_converges_on_closed_half_plane :=
    D.conclusion_prime_log_unweighted_euler_not_rh_pole_euler_converges_of_reciprocal_bound
      hReciprocal
  exact ⟨hEuler, hEuler 1 (by norm_num)⟩

end Omega.Conclusion
