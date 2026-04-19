import Omega.SPG.StokesGodelAlgorithmicHolographicCompleteness

namespace Omega.SPG

/-- Chapter-local package for the obstruction to computable fold sections hitting typical fiber
representatives. The structure packages a computable section together with an existing
Stokes--Gödel holographic-complexity witness and a fiber witness exhibiting a logarithmic
complexity gain somewhere in each fiber. -/
structure ComputableSectionCannotHitTypicalFiberData where
  holographicData : StokesGodelAlgorithmicHolographicCompletenessData
  computableSection : Prop
  fiberComplexityWitness : Prop
  computableSection_h : computableSection
  fiberComplexityWitness_h : fiberComplexityWitness
  sectionOutputComplexityUpperBound : Prop
  typicalFiberComplexityGain : Prop
  cannotHitTypicalFiber : Prop
  deriveSectionOutputComplexityUpperBound :
    computableSection → holographicData.complexityPreserved → sectionOutputComplexityUpperBound
  deriveTypicalFiberComplexityGain :
    fiberComplexityWitness → typicalFiberComplexityGain
  deriveCannotHitTypicalFiber :
    sectionOutputComplexityUpperBound → typicalFiberComplexityGain → cannotHitTypicalFiber

/-- Any computable section of the fold map has output complexity bounded by the base point, while
the existing fiber witness supplies a representative with logarithmic conditional-complexity gain.
Hence a computable section cannot systematically hit the typical high-complexity microstate in a
large fiber.
    prop:spg-computable-section-cannot-hit-typical-fiber -/
theorem paper_spg_computable_section_cannot_hit_typical_fiber
    (D : ComputableSectionCannotHitTypicalFiberData) :
    D.sectionOutputComplexityUpperBound ∧
      D.typicalFiberComplexityGain ∧
      D.cannotHitTypicalFiber := by
  have hComplexity :
      D.holographicData.complexityPreserved :=
    (paper_spg_stokes_godel_algorithmic_holographic_completeness D.holographicData).1
  have hUpper :
      D.sectionOutputComplexityUpperBound :=
    D.deriveSectionOutputComplexityUpperBound D.computableSection_h hComplexity
  have hGain : D.typicalFiberComplexityGain :=
    D.deriveTypicalFiberComplexityGain D.fiberComplexityWitness_h
  exact ⟨hUpper, hGain, D.deriveCannotHitTypicalFiber hUpper hGain⟩

end Omega.SPG
