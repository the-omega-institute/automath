import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part57bc-freezing-slope-coding-rate`. -/
theorem paper_xi_time_part57bc_freezing_slope_coding_rate
    (P : ℕ → ℝ) (aCrit : ℕ) (alphaStar betaMax gStar logTwo : ℝ)
    (hbeta : logTwo * betaMax = alphaStar)
    (hpressure : ∀ a, aCrit < a → P a = (a : ℝ) * alphaStar + gStar) :
    ∀ a, aCrit < a → P a = gStar + (a : ℝ) * logTwo * betaMax := by
  intro a ha
  rw [hpressure a ha, ← hbeta]
  ring

end Omega.Zeta
