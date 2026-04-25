import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-hellinger-toeplitz-inverse-localization`. -/
theorem paper_xi_hellinger_toeplitz_inverse_localization
    (toeplitz_symbol_model positive_symbol analytic_strip inverse_kernel_localization : Prop)
    (hModel : toeplitz_symbol_model) (hPos : positive_symbol)
    (hStrip : toeplitz_symbol_model -> positive_symbol -> analytic_strip)
    (hInv : analytic_strip -> inverse_kernel_localization) :
    toeplitz_symbol_model ∧ positive_symbol ∧ analytic_strip ∧
      inverse_kernel_localization := by
  exact ⟨hModel, hPos, hStrip hModel hPos, hInv (hStrip hModel hPos)⟩

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
