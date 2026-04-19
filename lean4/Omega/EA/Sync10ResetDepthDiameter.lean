import Mathlib.Tactic
import Omega.EA.Sync10ResetDepthSpectrum

namespace Omega.EA

/-- The reset-depth diameter of the `Sync10` target spectrum is `6`, and exactly two targets
realize that diameter.
    prop:sync10-reset-depth-diameter -/
theorem paper_sync10_reset_depth_diameter :
    And (∀ t : Sync10State, sync10ResetDepth t <= 6)
      (Finset.card (Finset.univ.filter fun t : Sync10State => sync10ResetDepth t = 6) = 2) := by
  rcases paper_sync10_reset_depth_spectrum with
    ⟨h000, h001, h002, h010, h100, h101, h0m12, h1m12, h01m1, h11m1, hExceptional⟩
  constructor
  · intro t
    cases t <;> simp [h000, h001, h002, h010, h100, h101, h0m12, h1m12, h01m1, h11m1]
  · have hcard := congrArg Finset.card hExceptional
    simpa using hcard

end Omega.EA
