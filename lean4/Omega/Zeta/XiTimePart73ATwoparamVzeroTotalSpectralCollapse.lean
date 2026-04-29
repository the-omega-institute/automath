import Mathlib.Tactic
import Omega.Zeta.RealInput40DetUv2plus8

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part73a-twoparam-vzero-total-spectral-collapse`. -/
theorem paper_xi_time_part73a_twoparam_vzero_total_spectral_collapse (z u : ℤ) :
    real_input_40_det_uv_2plus8_delta z u 0 = 1 - z := by
  unfold real_input_40_det_uv_2plus8_delta
  ring

end Omega.Zeta
