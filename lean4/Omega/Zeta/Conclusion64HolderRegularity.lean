import Mathlib

namespace Omega.Zeta

/-- Hölder regularity follows once the complex spectral gap and analytic control feed into the
absolute continuity package.
    cor:conclusion64-holder-regularity -/
theorem paper_conclusion64_holder_regularity
    (complexSpectralGap analyticControl absoluteContinuity holderRegularity : Prop)
    (hGap : complexSpectralGap) (hAnalytic : analyticControl)
    (hRegular :
      complexSpectralGap → analyticControl → absoluteContinuity ∧ holderRegularity) :
    absoluteContinuity ∧ holderRegularity := by
  exact hRegular hGap hAnalytic

end Omega.Zeta
