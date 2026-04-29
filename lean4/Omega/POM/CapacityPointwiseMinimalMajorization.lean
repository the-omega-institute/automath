import Mathlib.Tactic
import Omega.Conclusion.CapacityMajorizationSchurHardness

namespace Omega.POM

/-- Concrete two-profile package for the pointwise-minimal capacity versus majorization-maximal
comparison. The profile `extremizer` is tested against the single admissible competitor
`competitor`. -/
structure PointwiseMinimalMajorizationData where
  extremizer : List ℝ
  competitor : List ℝ

namespace PointwiseMinimalMajorizationData

/-- The admissible coarse-graining family recorded by the package. -/
def admissibleCoarseGrainings (D : PointwiseMinimalMajorizationData) : Set (List ℝ) :=
  {d | d = D.competitor}

/-- Pointwise minimality of the thresholded capacity functional. -/
def pointwiseMinimalCapacity (D : PointwiseMinimalMajorizationData) : Prop :=
  ∀ u : ℝ, Omega.Conclusion.capacityCurve D.extremizer u ≤
    Omega.Conclusion.capacityCurve D.competitor u

/-- Majorization maximality for the same pair of profiles. -/
def majorizationMaximal (D : PointwiseMinimalMajorizationData) : Prop :=
  Omega.Conclusion.majorizes D.extremizer D.competitor

lemma threshold_characterization (D : PointwiseMinimalMajorizationData) :
    D.pointwiseMinimalCapacity ↔ D.majorizationMaximal := by
  simpa [pointwiseMinimalCapacity, majorizationMaximal] using
    (Omega.Conclusion.paper_conclusion_capacity_majorization_schur_hardness D.extremizer
      D.competitor).symm

end PointwiseMinimalMajorizationData

open PointwiseMinimalMajorizationData

/-- Paper label: `cor:pom-capacity-pointwise-minimal-majorization`. -/
theorem paper_pom_capacity_pointwise_minimal_majorization
    (D : PointwiseMinimalMajorizationData) :
    D.pointwiseMinimalCapacity ↔ D.majorizationMaximal := by
  simpa using D.threshold_characterization

end Omega.POM
