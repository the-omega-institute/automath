import Mathlib.Tactic
import Omega.GU.Window6AffineFiberOrbitClassification

namespace Omega.GU

set_option maxHeartbeats 400000 in
/-- Paper-facing corollary for the degenerate window-6 shell splitting: the affine orbit counts are
`8/4/3/6`, the `d₆ = 4` shell splits into the affine-plane and simplex classes, and the zero-temperature
escort weights are therefore `1/3` and `2/3`.
    cor:window6-degenerate-shell-affine-splitting -/
theorem paper_window6_degenerate_shell_affine_splitting :
    window6AffineFiberOrbitCountL = 8 ∧
      window6AffineFiberOrbitCountPcirc = 4 ∧
      window6AffineFiberOrbitCountP = 3 ∧
      window6AffineFiberOrbitCountSigma = 6 ∧
      ((window6AffineFiberOrbitCountP : ℚ) /
          (window6AffineFiberOrbitCountP + window6AffineFiberOrbitCountSigma) = (1 : ℚ) / 3) ∧
      ((window6AffineFiberOrbitCountSigma : ℚ) /
          (window6AffineFiberOrbitCountP + window6AffineFiberOrbitCountSigma) = (2 : ℚ) / 3) := by
  rcases paper_window6_affine_fiber_orbit_classification with
    ⟨hL, hPcirc, hP, hSigma, _, _⟩
  refine ⟨hL, hPcirc, hP, hSigma, ?_, ?_⟩ <;>
    norm_num [window6AffineFiberOrbitCountP, window6AffineFiberOrbitCountSigma]

end Omega.GU
