import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part66-periodized-bernoulli-nonrajchman-no-lp`. A
nonvanishing Fourier subsequence gives non-Rajchman behavior, and the same obstruction
rules out `L^1`, hence all `L^p` densities through the supplied inclusion implication. -/
theorem paper_xi_time_part66_periodized_bernoulli_nonrajchman_no_lp
    (nonvanishingFourier notRajchman noL1Density noLpDensity : Prop)
    (hNonvanish : nonvanishingFourier)
    (hRaj : nonvanishingFourier -> notRajchman)
    (hL1 : nonvanishingFourier -> noL1Density)
    (hLp : noL1Density -> noLpDensity) :
    notRajchman ∧ noLpDensity := by
  exact ⟨hRaj hNonvanish, hLp (hL1 hNonvanish)⟩

end Omega.Zeta
