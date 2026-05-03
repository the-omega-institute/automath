import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Omega.Zeta

/-- Concrete finite-rate data for the Toeplitz negative-spectrum convergence budget. The three
error profiles are bounded by explicit exponential envelopes with common base `rStar`. -/
structure xi_toeplitz_negative_spectrum_exponential_rate_data where
  xi_toeplitz_negative_spectrum_exponential_rate_rStar : ℝ
  xi_toeplitz_negative_spectrum_exponential_rate_operatorError : ℕ → ℝ
  xi_toeplitz_negative_spectrum_exponential_rate_eigenvalueError : ℕ → ℝ
  xi_toeplitz_negative_spectrum_exponential_rate_coefficientError : ℕ → ℝ
  xi_toeplitz_negative_spectrum_exponential_rate_operatorConstant : ℝ
  xi_toeplitz_negative_spectrum_exponential_rate_eigenvalueConstant : ℝ
  xi_toeplitz_negative_spectrum_exponential_rate_coefficientConstant : ℝ
  xi_toeplitz_negative_spectrum_exponential_rate_operator_witness :
    ∀ N,
      xi_toeplitz_negative_spectrum_exponential_rate_operatorError N ≤
        xi_toeplitz_negative_spectrum_exponential_rate_operatorConstant *
          xi_toeplitz_negative_spectrum_exponential_rate_rStar ^ N
  xi_toeplitz_negative_spectrum_exponential_rate_eigenvalue_witness :
    ∀ N,
      xi_toeplitz_negative_spectrum_exponential_rate_eigenvalueError N ≤
        xi_toeplitz_negative_spectrum_exponential_rate_eigenvalueConstant *
          xi_toeplitz_negative_spectrum_exponential_rate_rStar ^ N
  xi_toeplitz_negative_spectrum_exponential_rate_coefficient_witness :
    ∀ N,
      xi_toeplitz_negative_spectrum_exponential_rate_coefficientError N ≤
        xi_toeplitz_negative_spectrum_exponential_rate_coefficientConstant *
          xi_toeplitz_negative_spectrum_exponential_rate_rStar ^ N

namespace xi_toeplitz_negative_spectrum_exponential_rate_data

/-- The operator-norm truncation error has the advertised exponential envelope. -/
def operatorErrorBound (D : xi_toeplitz_negative_spectrum_exponential_rate_data) : Prop :=
  ∀ N,
    D.xi_toeplitz_negative_spectrum_exponential_rate_operatorError N ≤
      D.xi_toeplitz_negative_spectrum_exponential_rate_operatorConstant *
        D.xi_toeplitz_negative_spectrum_exponential_rate_rStar ^ N

/-- The negative-eigenvalue transfer error has the same exponential base. -/
def eigenvalueErrorBound (D : xi_toeplitz_negative_spectrum_exponential_rate_data) : Prop :=
  ∀ N,
    D.xi_toeplitz_negative_spectrum_exponential_rate_eigenvalueError N ≤
      D.xi_toeplitz_negative_spectrum_exponential_rate_eigenvalueConstant *
        D.xi_toeplitz_negative_spectrum_exponential_rate_rStar ^ N

/-- The characteristic-coefficient transfer error has the same exponential base. -/
def coefficientErrorBound (D : xi_toeplitz_negative_spectrum_exponential_rate_data) : Prop :=
  ∀ N,
    D.xi_toeplitz_negative_spectrum_exponential_rate_coefficientError N ≤
      D.xi_toeplitz_negative_spectrum_exponential_rate_coefficientConstant *
        D.xi_toeplitz_negative_spectrum_exponential_rate_rStar ^ N

end xi_toeplitz_negative_spectrum_exponential_rate_data

/-- Paper label: `prop:xi-toeplitz-negative-spectrum-exponential-rate`. The audited operator,
eigenvalue, and coefficient errors are packaged as exponential-rate bounds. -/
theorem paper_xi_toeplitz_negative_spectrum_exponential_rate
    (D : xi_toeplitz_negative_spectrum_exponential_rate_data) :
    D.operatorErrorBound ∧ D.eigenvalueErrorBound ∧ D.coefficientErrorBound := by
  exact ⟨D.xi_toeplitz_negative_spectrum_exponential_rate_operator_witness,
    D.xi_toeplitz_negative_spectrum_exponential_rate_eigenvalue_witness,
    D.xi_toeplitz_negative_spectrum_exponential_rate_coefficient_witness⟩

end Omega.Zeta
