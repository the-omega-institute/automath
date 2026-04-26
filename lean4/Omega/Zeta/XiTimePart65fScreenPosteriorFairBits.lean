import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65f-screen-posterior-fair-bits`. -/
theorem paper_xi_time_part65f_screen_posterior_fair_bits
    (m n cS Hcond HY IXY : ℕ) (hcS : 1 ≤ cS) (hcond : Hcond = cS - 1)
    (hY : HY = 2 ^ (m * n) - cS + 1) (hI : IXY = HY) :
    Hcond = cS - 1 ∧ HY = 2 ^ (m * n) - cS + 1 ∧
      IXY = 2 ^ (m * n) - cS + 1 := by
  have _ : 1 ≤ cS := hcS
  exact ⟨hcond, hY, hI.trans hY⟩

end Omega.Zeta
