import Mathlib.Tactic

namespace Omega.Zeta

/-- Variance readout from the quartic KL asymptotic constant.
    cor:xi-cauchy-poisson-kl-variance-readout -/
theorem paper_xi_cauchy_poisson_kl_variance_readout
    (sigma L : ℝ)
    (hsigma : 0 ≤ sigma)
    (hL : L = sigma ^ 4 / 8) :
    sigma ^ 2 = Real.sqrt (8 * L) := by
  have hsigma_sq : 0 ≤ sigma ^ 2 := pow_nonneg hsigma 2
  calc
    sigma ^ 2 = Real.sqrt ((sigma ^ 2) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsigma_sq]
    _ = Real.sqrt (8 * L) := by
      congr 1
      rw [hL]
      ring

end Omega.Zeta
