import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-hellinger-toeplitz-bandwidth-sharpness`. -/
theorem paper_xi_hellinger_toeplitz_bandwidth_sharpness (Delta aMax : ℝ)
    (superThresholdDecay : Prop) (hDelta : 0 < Delta) (hanalytic : Delta / 2 ≤ aMax)
    (hpoles : aMax ≤ Delta / 2)
    (hdecay_forces_wider_band : superThresholdDecay → Delta / 2 < aMax) :
    aMax = Delta / 2 ∧ ¬ superThresholdDecay := by
  have _ : 0 < Delta := hDelta
  refine ⟨le_antisymm hpoles hanalytic, ?_⟩
  intro hdecay
  exact (not_lt_of_ge hpoles) (hdecay_forces_wider_band hdecay)

end Omega.Zeta
