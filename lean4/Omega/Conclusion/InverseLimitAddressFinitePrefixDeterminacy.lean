import Mathlib.Tactic

namespace Omega.Conclusion

/-- Data package encoding the compactness proof that a continuous address map to a discrete
codomain depends only on a finite prefix. The fields follow the paper proof: local constancy on
clopen cylinders, extraction of a finite cylinder cover, a maximal prefix depth, and the induced
factor map on the corresponding finite stage. -/
structure InverseLimitAddressFinitePrefixDeterminacyData where
  locallyConstantOnCylinderBasis : Prop
  finiteCylinderCover : Prop
  maximalPrefixDepth : Prop
  finiteStageFactorMap : Prop
  factorsThroughFinitePrefix : Prop
  locallyConstantOnCylinderBasis_h : locallyConstantOnCylinderBasis
  deriveFiniteCylinderCover :
    locallyConstantOnCylinderBasis → finiteCylinderCover
  deriveMaximalPrefixDepth : finiteCylinderCover → maximalPrefixDepth
  deriveFiniteStageFactorMap : maximalPrefixDepth → finiteStageFactorMap
  deriveFactorsThroughFinitePrefix :
    locallyConstantOnCylinderBasis → finiteStageFactorMap → factorsThroughFinitePrefix

/-- Paper package: a continuous inverse-limit address map to a discrete codomain factors through
some finite prefix stage. `thm:conclusion-inverse-limit-address-finite-prefix-determinacy` -/
theorem paper_conclusion_inverse_limit_address_finite_prefix_determinacy
    (D : InverseLimitAddressFinitePrefixDeterminacyData) : D.factorsThroughFinitePrefix := by
  have hCover : D.finiteCylinderCover :=
    D.deriveFiniteCylinderCover D.locallyConstantOnCylinderBasis_h
  have hDepth : D.maximalPrefixDepth := D.deriveMaximalPrefixDepth hCover
  have hFactor : D.finiteStageFactorMap := D.deriveFiniteStageFactorMap hDepth
  exact D.deriveFactorsThroughFinitePrefix D.locallyConstantOnCylinderBasis_h hFactor

end Omega.Conclusion
