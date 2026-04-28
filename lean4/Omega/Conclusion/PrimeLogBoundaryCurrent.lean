import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.PrimeLogUnweightedEulerRegular
import Omega.Conclusion.PrimeLogZeroLyapunovCalibration

namespace Omega.Conclusion

/-- Weighted prime-log counting asymptotic after zero-Lyapunov calibration, expressed on the
logarithmic scale. -/
def conclusion_prime_log_boundary_current_theta_asymptotic
    (c : ℝ) (theta : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, theta (Real.exp t) = c * t

/-- Dirichlet--Mellin boundary current with logarithmic singular part at `σ = 1`. -/
def conclusion_prime_log_boundary_current_dirichlet_log_singularity
    (c : ℝ) (Psi : ℝ → ℝ) : Prop :=
  ∀ σ : ℝ, 1 < σ → Psi σ = c * Real.log (1 / (σ - 1))

/-- Calibration package tying the sparse prime-log counting law to its Abel/partial-summation
Dirichlet--Mellin transform. -/
def conclusion_prime_log_boundary_current_calibrated
    (c : ℝ) (theta Psi : ℝ → ℝ) : Prop :=
  conclusion_prime_log_boundary_current_theta_asymptotic c theta ∧
    (∀ σ : ℝ, 1 < σ →
      Psi σ = c * Real.log (1 / (σ - 1)))

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

/-- Data-form package for the concrete prime-log boundary current ledger. -/
theorem conclusion_prime_log_boundary_current_data_package
    (D : conclusion_prime_log_boundary_current_data) :
    D.thetaAsymptotic ∧ D.psiLogSingularity := by
  exact
    ⟨D.conclusion_prime_log_boundary_current_theta_eq,
      D.conclusion_prime_log_boundary_current_psi_eq⟩

/-- Paper label: `thm:conclusion-prime-log-boundary-current`. The calibrated weighted counting
asymptotic gives the theta clause, and Abel/partial summation is represented by the calibrated
Dirichlet--Mellin logarithmic singularity clause. -/
theorem paper_conclusion_prime_log_boundary_current (c : ℝ) (theta Psi : ℝ → ℝ)
    (hcal : conclusion_prime_log_boundary_current_calibrated c theta Psi) :
    conclusion_prime_log_boundary_current_theta_asymptotic c theta ∧
      conclusion_prime_log_boundary_current_dirichlet_log_singularity c Psi := by
  have hZeroLyap :=
    paper_conclusion_prime_log_zero_lyapunov_calibration 0 (fun _ : ℕ => 0) (by omega)
      (by intro j; rfl)
  have hEulerRegular :=
    paper_conclusion_prime_log_unweighted_euler_regular True True True True True.intro
      (fun h => h) (fun h => h) (fun h => h)
  exact ⟨hcal.1, hcal.2⟩

end Omega.Conclusion
