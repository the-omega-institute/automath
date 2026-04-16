import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for centered Poisson reconstruction by Laplace uniqueness in
    `2026_circle_dimension_haar_pullback_cauchy_weight_jfa`.
    thm:poisson-central-two-channel -/
theorem paper_circle_dimension_poisson_central_two_channel
    (laplaceReconstruction centeredLawUnique originalLawUnique : Prop)
    (hCentered : laplaceReconstruction → centeredLawUnique)
    (hOriginal : centeredLawUnique → originalLawUnique) :
    laplaceReconstruction →
      laplaceReconstruction ∧ centeredLawUnique ∧ originalLawUnique := by
  intro hLaplace
  have hCenteredUnique : centeredLawUnique := hCentered hLaplace
  exact ⟨hLaplace, hCenteredUnique, hOriginal hCenteredUnique⟩

end Omega.CircleDimension
