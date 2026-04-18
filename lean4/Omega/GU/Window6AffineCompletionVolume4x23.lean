import Mathlib.Tactic
import Omega.GU.Window6AffineFiberOrbitClassification

namespace Omega.GU

/-- The window-6 affine orbit counts `8/4/3/6` give affine-completion volume `92 = 4 * 23`, and
the corresponding weighted completion average is exactly `5`.
    thm:window6-affine-completion-volume-4x23 -/
theorem paper_window6_affine_completion_volume_4x23 :
    let affineCompletion : ℕ := 8 * 2 + 4 * 4 + 3 * 4 + 6 * 8
    let weightedCompletion : ℚ := ((8 : ℚ) * 2 * 2 + 4 * 3 * 4 + 3 * 4 * 4 + 6 * 4 * 8) / 64
    affineCompletion = 92 ∧ affineCompletion = 4 * 23 ∧ weightedCompletion = 5 := by
  rcases paper_window6_affine_fiber_orbit_classification with ⟨hL, hPcirc, hP, hSigma, _, _⟩
  have hCounts :
      window6AffineFiberOrbitCountL = 8 ∧
        window6AffineFiberOrbitCountPcirc = 4 ∧
        window6AffineFiberOrbitCountP = 3 ∧
        window6AffineFiberOrbitCountSigma = 6 := by
    exact ⟨hL, hPcirc, hP, hSigma⟩
  norm_num

end Omega.GU
