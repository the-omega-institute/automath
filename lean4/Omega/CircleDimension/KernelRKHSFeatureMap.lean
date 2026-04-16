import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local wrapper for the explicit feature-map package of the difference kernel
`K(a,b) = 2 / (4 + (a - b)^2)`. The wrapper records that the spectral kernel formula has already
been assembled in the chapter, from which one obtains the feature-map identity, the resulting
Moore--Aronszajn RKHS characterization, the projection-norm criterion, and the reproducing
property. -/
structure KernelRKHSFeatureMapData where
  spectralKernelFormula : Prop
  featureMapDefined : Prop
  featureMapIdentity : Prop
  rkhsCharacterization : Prop
  projectionNormCharacterization : Prop
  reproducingProperty : Prop
  spectralKernelFormula_h : spectralKernelFormula
  defineFeatureMap : spectralKernelFormula → featureMapDefined
  deriveFeatureMapIdentity : featureMapDefined → featureMapIdentity
  deriveRkhsCharacterization : featureMapDefined → rkhsCharacterization
  deriveProjectionNormCharacterization :
    featureMapDefined → projectionNormCharacterization
  deriveReproducingProperty : featureMapDefined → reproducingProperty

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the explicit feature map of the CircleDimension difference kernel.
    prop:cdim-kernel-rkhs-feature-map -/
theorem paper_cdim_kernel_rkhs_feature_map (D : KernelRKHSFeatureMapData) :
    D.featureMapIdentity ∧ D.rkhsCharacterization ∧ D.projectionNormCharacterization ∧
      D.reproducingProperty := by
  have hFeatureMap : D.featureMapDefined := D.defineFeatureMap D.spectralKernelFormula_h
  exact ⟨D.deriveFeatureMapIdentity hFeatureMap, D.deriveRkhsCharacterization hFeatureMap,
    D.deriveProjectionNormCharacterization hFeatureMap, D.deriveReproducingProperty hFeatureMap⟩

end Omega.CircleDimension
