import Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure

namespace Omega.PhysicalSpacetimeSkeleton

universe u

open Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure

/-- Chapter-local package for the descended global metric on the maximal admissible quotient
domain. The local Levi-Civita and curvature objects are uniquely determined by this metric in the
paper narrative, so only the gluing-relevant field is recorded here. -/
structure GlobalGeometricObjects {ι : Type u} [Fintype ι]
    (F : CompatibleLorentzFamily ι) where
  metric : maximalAdmissibleDomain F → ℝ

/-- Paper-facing existence/uniqueness wrapper for the global geometric objects on the maximal
admissible quotient domain.
    prop:physical-spacetime-global-geometric-objects -/
theorem paper_physical_spacetime_global_geometric_objects :
    ∀ {ι : Type u} [Fintype ι] (F : CompatibleLorentzFamily ι),
      ∃! G : GlobalGeometricObjects F,
        ∀ i x, G.metric (pointClass F i x) = F.metric i x := by
  intro ι _ F
  refine ⟨⟨globalMetric F⟩, ?_, ?_⟩
  · intro i x
    rfl
  · intro G hG
    cases G with
    | mk metric =>
        have hmetric : metric = globalMetric F := by
          funext q
          refine Quotient.inductionOn q ?_
          intro p
          rcases p with ⟨i, x⟩
          calc
            metric (pointClass F i x) = F.metric i x := by simpa using hG i x
            _ = globalMetric F (pointClass F i x) := by rfl
        cases hmetric
        rfl

end Omega.PhysicalSpacetimeSkeleton
