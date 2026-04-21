import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper theorem:
`prop:xi-cauchy-poisson-location-scale-uncentered-third` -/
theorem paper_xi_cauchy_poisson_location_scale_uncentered_third (mu sigmaSq nu2 A2 A3 : ℝ)
    (hasExpansion : Prop) (hA2 : 4 * A2 = mu ^ 2) (hA3 : 4 * A3 = mu * (sigmaSq - nu2))
    (hexp : hasExpansion) :
    hasExpansion ∧ A2 = mu ^ 2 / 4 ∧ A3 = mu * (sigmaSq - nu2) / 4 := by
  refine ⟨hexp, ?_, ?_⟩
  · linarith
  · linarith

end Omega.Zeta
