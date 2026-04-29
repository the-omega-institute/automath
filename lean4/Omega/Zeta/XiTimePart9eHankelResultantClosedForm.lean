import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- Paper label: `thm:xi-time-part9e-hankel-resultant-closed-form`. -/
theorem paper_xi_time_part9e_hankel_resultant_closed_form {kappa : Nat} {K : Type*}
    [Field K] (b c : Fin (kappa + 1) -> K) (resultant : K)
    (hres :
      (Matrix.vandermonde b).det ^ 2 * (Finset.univ.prod c) =
        (-1 : K) ^ (kappa * (kappa + 1) / 2) * resultant) :
    Matrix.det ((Matrix.vandermonde b) * Matrix.diagonal c *
        (Matrix.vandermonde b).transpose) =
      (-1 : K) ^ (kappa * (kappa + 1) / 2) * resultant := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
  rw [← hres]
  ring

end Omega.Zeta
