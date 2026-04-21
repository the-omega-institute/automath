import Mathlib.Tactic


namespace Omega.CircleDimension

/-- Paper-facing wrapper for the dyadic Stokes reconstruction corollary: the normalized holonomy
curvature field and its `L²` energy converge together exactly as supplied by the reconstruction
theorem.
    cor:cdim-dyadic-holonomy-curvature-limit -/
theorem paper_cdim_dyadic_holonomy_curvature_limit
    (normalizedCurvatureConvergesL2 energyConverges : Prop)
    (hReconstruction : normalizedCurvatureConvergesL2 ∧ energyConverges) :
    normalizedCurvatureConvergesL2 ∧ energyConverges := by
  exact hReconstruction

end Omega.CircleDimension
