import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-poisson-cauchy-mixture-point-leading-constants`. The common
variance scale cancels between the KL and TV leading terms. -/
theorem paper_xi_poisson_cauchy_mixture_point_leading_constants
    (variance tvLeading klLeading : ℝ) (hvar : variance ≠ 0)
    (htv : tvLeading = (3 * Real.sqrt 3 / (4 * Real.pi)) * variance)
    (hkl : klLeading = variance ^ 2 / 8) :
    klLeading / tvLeading ^ 2 = 2 * Real.pi ^ 2 / 27 := by
  have hsqrt3_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)]
  have hsqrt3_ne : (Real.sqrt 3 : ℝ) ≠ 0 := by positivity
  rw [hkl, htv]
  field_simp [hvar, Real.pi_ne_zero, hsqrt3_ne]
  nlinarith [hsqrt3_sq]

end Omega.Zeta
