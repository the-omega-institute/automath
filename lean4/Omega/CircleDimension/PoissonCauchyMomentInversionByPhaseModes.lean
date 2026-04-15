import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing phase-mode wrapper: finite Laurent support and mode orthogonality reduce
the Poisson--Cauchy moment readout to three explicit coefficients, from which the centered second,
third, and fourth moments are recovered directly.
    prop:cdim-poisson-cauchy-moment-inversion-by-phase-modes -/
theorem paper_cdim_poisson_cauchy_moment_inversion_by_phase_modes
    (finiteLaurentModes fourierOrthogonality : Prop)
    {sigmaSq mu3 mu4 mode2 mode3 mode4 : ℝ}
    (hLaurent : finiteLaurentModes)
    (hOrthogonal : fourierOrthogonality)
    (hMode2 : mode2 = -sigmaSq / 4)
    (hMode3 : mode3 = mu3 / 8)
    (hMode4 : mode4 = mu4 / 16) :
    finiteLaurentModes ∧ fourierOrthogonality ∧
      sigmaSq = -4 * mode2 ∧ mu3 = 8 * mode3 ∧ mu4 = 16 * mode4 := by
  refine ⟨hLaurent, hOrthogonal, ?_, ?_, ?_⟩ <;> nlinarith

end Omega.CircleDimension
