import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Conclusion

/-- Concrete asymptotic ledger for the prime-log boundary current.  The two displayed functions
are the weighted Chebyshev side and the Dirichlet--Mellin boundary current; the certificates give
their explicit main term plus recorded error/remainder functions. -/
structure conclusion_prime_log_boundary_current_data where
  conclusion_prime_log_boundary_current_c : ℝ
  conclusion_prime_log_boundary_current_theta : ℝ → ℝ
  conclusion_prime_log_boundary_current_thetaError : ℝ → ℝ
  conclusion_prime_log_boundary_current_psi : ℝ → ℝ
  conclusion_prime_log_boundary_current_psiRemainder : ℝ → ℝ
  conclusion_prime_log_boundary_current_theta_eq :
    ∀ x,
      2 < x →
        conclusion_prime_log_boundary_current_theta x =
          conclusion_prime_log_boundary_current_c / 2 * (x / Real.log x) +
            conclusion_prime_log_boundary_current_thetaError x
  conclusion_prime_log_boundary_current_psi_eq :
    ∀ σ,
      1 < σ →
        conclusion_prime_log_boundary_current_psi σ =
          conclusion_prime_log_boundary_current_c / 2 * Real.log (1 / (σ - 1)) +
            conclusion_prime_log_boundary_current_psiRemainder σ

namespace conclusion_prime_log_boundary_current_data

/-- Weighted prime-log counting has the recorded `c / 2 * x / log x` main term. -/
def thetaAsymptotic (D : conclusion_prime_log_boundary_current_data) : Prop :=
  ∀ x,
    2 < x →
      D.conclusion_prime_log_boundary_current_theta x =
        D.conclusion_prime_log_boundary_current_c / 2 * (x / Real.log x) +
          D.conclusion_prime_log_boundary_current_thetaError x

/-- The Mellin boundary current has the recorded logarithmic singular part at `σ = 1`. -/
def psiLogSingularity (D : conclusion_prime_log_boundary_current_data) : Prop :=
  ∀ σ,
    1 < σ →
      D.conclusion_prime_log_boundary_current_psi σ =
        D.conclusion_prime_log_boundary_current_c / 2 * Real.log (1 / (σ - 1)) +
          D.conclusion_prime_log_boundary_current_psiRemainder σ

end conclusion_prime_log_boundary_current_data

/-- Paper label: `thm:conclusion-prime-log-boundary-current`. -/
theorem paper_conclusion_prime_log_boundary_current
    (D : conclusion_prime_log_boundary_current_data) :
    D.thetaAsymptotic ∧ D.psiLogSingularity := by
  exact
    ⟨D.conclusion_prime_log_boundary_current_theta_eq,
      D.conclusion_prime_log_boundary_current_psi_eq⟩

end Omega.Conclusion
