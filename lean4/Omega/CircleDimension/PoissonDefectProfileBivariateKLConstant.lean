import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper label: `prop:cdim-poisson-defect-profile-bivariate-kl-constant`.
This is the paper-facing specialization of the bivariate Poisson KL constant once the weighted
defect-profile bookkeeping has been reduced to the explicit closed formula `hFormula`. -/
theorem paper_cdim_poisson_defect_profile_bivariate_kl_constant
    (varianceGap covariance klLimit : ℝ)
    (hFormula : klLimit = (varianceGap ^ 2) / 8 + (covariance ^ 2) / 2) :
    klLimit = (varianceGap ^ 2) / 8 + (covariance ^ 2) / 2 := by
  exact hFormula

end Omega.CircleDimension
