import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the negative Toeplitz regularized determinant limit.  The logarithms
converge to the logarithm of a positive limiting determinant, and each finite determinant is
the exponential of its logged regularized determinant. -/
structure xi_toeplitz_negative_regularized_determinant_limit_data where
  logNegativeRegularizedDeterminant : ℕ → ℝ
  negativeRegularizedDeterminant : ℕ → ℝ
  limitingDeterminant : ℝ
  positiveLimit : 0 < limitingDeterminant
  determinant_eq_exp_log :
    ∀ n, negativeRegularizedDeterminant n = Real.exp (logNegativeRegularizedDeterminant n)
  log_converges :
    Filter.Tendsto logNegativeRegularizedDeterminant Filter.atTop
      (nhds (Real.log limitingDeterminant))

/-- The determinant convergence obtained from logarithmic convergence. -/
def xi_toeplitz_negative_regularized_determinant_limit_statement
    (D : xi_toeplitz_negative_regularized_determinant_limit_data) : Prop :=
  Filter.Tendsto D.negativeRegularizedDeterminant Filter.atTop (nhds D.limitingDeterminant)

/-- Paper label: `cor:xi-toeplitz-negative-regularized-determinant-limit`. -/
theorem paper_xi_toeplitz_negative_regularized_determinant_limit
    (D : xi_toeplitz_negative_regularized_determinant_limit_data) :
    xi_toeplitz_negative_regularized_determinant_limit_statement D := by
  have hexp :
      Filter.Tendsto (fun x : ℝ => Real.exp x) (nhds (Real.log D.limitingDeterminant))
        (nhds (Real.exp (Real.log D.limitingDeterminant))) :=
    Real.continuous_exp.tendsto _
  have hcomp :
      Filter.Tendsto (fun n => Real.exp (D.logNegativeRegularizedDeterminant n))
        Filter.atTop (nhds (Real.exp (Real.log D.limitingDeterminant))) :=
    hexp.comp D.log_converges
  have hdet :
      (fun n => Real.exp (D.logNegativeRegularizedDeterminant n)) =
        D.negativeRegularizedDeterminant := by
    funext n
    exact (D.determinant_eq_exp_log n).symm
  have hlimit : Real.exp (Real.log D.limitingDeterminant) = D.limitingDeterminant :=
    Real.exp_log D.positiveLimit
  simpa [xi_toeplitz_negative_regularized_determinant_limit_statement, hdet, hlimit] using hcomp

end Omega.Zeta
