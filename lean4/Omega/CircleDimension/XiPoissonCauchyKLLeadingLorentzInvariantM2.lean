import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper label: `cor:xi-poisson-cauchy-kl-leading-lorentz-invariant-m2`. -/
theorem paper_xi_poisson_cauchy_kl_leading_lorentz_invariant_m2
    (varGamma varA cov leading : Real)
    (hleading : leading = ((varGamma - varA) ^ 2 + 4 * cov ^ 2) / 8) :
    leading = 0 ↔ varGamma = varA ∧ cov = 0 := by
  constructor
  · intro hzero
    have hsum : (varGamma - varA) ^ 2 + 4 * cov ^ 2 = 0 := by
      nlinarith
    have hgap_sq : (varGamma - varA) ^ 2 = 0 := by
      nlinarith [sq_nonneg (varGamma - varA), sq_nonneg cov]
    have hcov_sq : cov ^ 2 = 0 := by
      nlinarith [sq_nonneg (varGamma - varA), sq_nonneg cov]
    constructor
    · have hgap : varGamma - varA = 0 := by
        nlinarith [sq_nonneg (varGamma - varA)]
      linarith
    · nlinarith [sq_nonneg cov]
  · rintro ⟨hvar, hcov⟩
    subst varGamma
    subst cov
    norm_num [hleading]

end Omega.CircleDimension
