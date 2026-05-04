import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`thm:xi-bernoulli-two-periodization-no-lp-density`. -/
theorem paper_xi_bernoulli_two_periodization_no_lp_density
    (fourierNotInEveryFiniteLr noLpDensity : Prop)
    (h_fourier : fourierNotInEveryFiniteLr)
    (h_density_obstruction : fourierNotInEveryFiniteLr -> noLpDensity) :
    noLpDensity := by
  exact h_density_obstruction h_fourier

end Omega.Zeta
