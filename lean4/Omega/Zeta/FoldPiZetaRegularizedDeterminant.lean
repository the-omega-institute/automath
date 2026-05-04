import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zbh-foldpi-zeta-regularized-determinant`. -/
theorem paper_xi_time_part9zbh_foldpi_zeta_regularized_determinant
    (φ detζ deriv0 : ℝ) (exp log : ℝ → ℝ)
    (hderiv : deriv0 = - log φ)
    (hdet : detζ = exp (-deriv0))
    (hexpLog : exp (log φ) = φ) :
    detζ = φ := by
  rw [hdet, hderiv]
  simpa using hexpLog

end Omega.Zeta
