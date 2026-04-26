import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-CMV data for endpoint-flux approximation. -/
structure xi_endpoint_flux_finite_cmv_computable_data where
  schurDegree : ℕ
  exactFlux : ℕ → ℝ
  truncatedFlux : ℕ → ℝ
  rationalEstimator : ℕ → ℚ
  C : ℝ
  q : ℝ
  hC_nonneg : 0 ≤ C
  hq_pos : 0 < q
  hq_lt_one : q < 1
  h_finite_schur_termination :
    ∀ N, schurDegree ≤ N → truncatedFlux N = exactFlux N
  h_initial_error :
    ∀ N, N < schurDegree → |truncatedFlux N - exactFlux N| ≤ C * q ^ N
  h_rational_estimator :
    ∀ N, (rationalEstimator N : ℝ) = truncatedFlux N

/-- Finite Schur termination makes every truncation past the Blaschke degree exact. -/
def xi_endpoint_flux_finite_cmv_computable_data.finite_exact
    (D : xi_endpoint_flux_finite_cmv_computable_data) : Prop :=
  ∀ N, D.schurDegree ≤ N → D.truncatedFlux N = D.exactFlux N

/-- The finite initial segment is controlled by a geometric envelope. -/
def xi_endpoint_flux_finite_cmv_computable_data.exponential_error_bound
    (D : xi_endpoint_flux_finite_cmv_computable_data) : Prop :=
  0 ≤ D.C ∧ 0 < D.q ∧ D.q < 1 ∧
    ∀ N, |D.truncatedFlux N - D.exactFlux N| ≤ D.C * D.q ^ N

/-- The estimator is given by a finite rational recursion/evaluation certificate. -/
def xi_endpoint_flux_finite_cmv_computable_data.estimator_computable
    (D : xi_endpoint_flux_finite_cmv_computable_data) : Prop :=
  ∃ rationalEvaluation : ℕ → ℚ, ∀ N, (rationalEvaluation N : ℝ) = D.truncatedFlux N

/-- Paper label: `thm:xi-endpoint-flux-finite-cmv-computable`. -/
theorem paper_xi_endpoint_flux_finite_cmv_computable
    (D : xi_endpoint_flux_finite_cmv_computable_data) :
    D.finite_exact ∧ D.exponential_error_bound ∧ D.estimator_computable := by
  refine ⟨?_, ?_, ?_⟩
  · exact D.h_finite_schur_termination
  · refine ⟨D.hC_nonneg, D.hq_pos, D.hq_lt_one, ?_⟩
    intro N
    by_cases hN : N < D.schurDegree
    · exact D.h_initial_error N hN
    · have hdeg : D.schurDegree ≤ N := Nat.le_of_not_gt hN
      have hdiff : D.truncatedFlux N - D.exactFlux N = 0 := by
        rw [D.h_finite_schur_termination N hdeg]
        ring
      calc
        |D.truncatedFlux N - D.exactFlux N| = 0 := by rw [hdiff, abs_zero]
        _ ≤ D.C * D.q ^ N := mul_nonneg D.hC_nonneg (pow_nonneg (le_of_lt D.hq_pos) N)
  · exact ⟨D.rationalEstimator, D.h_rational_estimator⟩

end Omega.Zeta
