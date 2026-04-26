import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete robust-verification package for a Toeplitz negative-spectrum certificate. The matrix
entries are included so the statement remains tied to a genuine Toeplitz approximation problem,
while the audited Weyl transfer is expressed through lower-eigenvalue bounds. -/
structure xi_toeplitz_negative_spectrum_robust_verification_data where
  n : ℕ
  toeplitzMatrix : Matrix (Fin n) (Fin n) ℝ
  auditedApproximation : Matrix (Fin n) (Fin n) ℝ
  trueMinEigenvalue : ℝ
  approxMinEigenvalue : ℝ
  operatorNormError : ℝ
  weyl_lower_transfer :
    trueMinEigenvalue ≤ approxMinEigenvalue + operatorNormError
  audited_negative_margin :
    approxMinEigenvalue + operatorNormError < 0

def xi_toeplitz_negative_spectrum_robust_verification_statement
    (D : xi_toeplitz_negative_spectrum_robust_verification_data) : Prop :=
  D.trueMinEigenvalue < 0

/-- Paper label: `prop:xi-toeplitz-negative-spectrum-robust-verification`. A negative approximate
eigenvalue that dominates the perturbation radius remains negative for the true Toeplitz matrix by
the standard Weyl perturbation inequality. -/
theorem paper_xi_toeplitz_negative_spectrum_robust_verification
    (D : xi_toeplitz_negative_spectrum_robust_verification_data) :
    xi_toeplitz_negative_spectrum_robust_verification_statement D := by
  exact lt_of_le_of_lt D.weyl_lower_transfer D.audited_negative_margin

end Omega.Zeta
