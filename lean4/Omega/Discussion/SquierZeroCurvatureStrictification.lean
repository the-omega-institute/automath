import Mathlib.Tactic
import Omega.Discussion.HypercubePotentialCurvatureControlledStrictification
import Omega.Discussion.SquierCurvatureHolonomyStokes

namespace Omega.Discussion

/-- Chapter-local package for the zero-curvature strictification corollary. The fields isolate the
vanishing-class criterion identifying zero curvature with the existence of a potential and the
resulting `H¹`-torsor of strictifications once such a potential is chosen. -/
structure SquierZeroCurvatureStrictificationData where
  zeroCurvature : Prop
  hasPotential : Prop
  strictificationTorsor : Prop
  vanishingClassCriterion : zeroCurvature ↔ hasPotential
  exactnessToStrictification : hasPotential → strictificationTorsor

/-- Paper-facing wrapper for the zero-curvature strictification criterion: vanishing Squier
curvature is equivalent to admitting a potential, and any such potential determines the expected
strictification torsor.
    cor:discussion-squier-zero-curvature-strictification -/
theorem paper_discussion_squier_zero_curvature_strictification
    (D : SquierZeroCurvatureStrictificationData) :
    (D.zeroCurvature ↔ D.hasPotential) ∧ (D.hasPotential → D.strictificationTorsor) := by
  exact ⟨D.vanishingClassCriterion, D.exactnessToStrictification⟩

end Omega.Discussion
