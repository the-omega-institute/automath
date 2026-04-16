import Omega.CircleDimension.KernelRKHSFeatureMap

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local data for the finite-rank RKHS interpretation of the typed-address comoving
kernel `K_ν`. The explicit rank-one kernel expansion feeds into the CircleDimension feature-map
wrapper, and the diagonal restriction identifies the boundary scalar profile `H_ν`. -/
structure ComovingRKHSData where
  explicitKernelFiniteRankSum : Prop
  boundaryScalarProfile : Prop
  explicitKernelFiniteRankSum_h : explicitKernelFiniteRankSum
  boundaryScalarProfile_h : boundaryScalarProfile
  kernelFeatureMapData : Omega.CircleDimension.KernelRKHSFeatureMapData
  finiteRankKernel : Prop
  finiteRankRKHS : Prop
  boundaryScalarDiagonalRestriction : Prop
  deriveFiniteRankKernel :
    explicitKernelFiniteRankSum → finiteRankKernel
  deriveFiniteRankRKHS :
    finiteRankKernel → kernelFeatureMapData.rkhsCharacterization → finiteRankRKHS
  deriveBoundaryScalarDiagonalRestriction :
    boundaryScalarProfile →
      kernelFeatureMapData.featureMapIdentity →
      kernelFeatureMapData.reproducingProperty →
      boundaryScalarDiagonalRestriction

/-- The explicit finite sum for `K_ν` exhibits a finite-rank kernel, the CircleDimension
feature-map wrapper gives the resulting RKHS package, and the boundary scalar `H_ν` is the
diagonal restriction of the same kernel object.
    thm:typed-address-biaxial-completion-comoving-rkhs -/
theorem paper_typed_address_biaxial_completion_comoving_rkhs
    (D : ComovingRKHSData) :
    D.finiteRankKernel ∧ D.finiteRankRKHS ∧ D.boundaryScalarDiagonalRestriction := by
  have hFeatureMap :
      D.kernelFeatureMapData.featureMapIdentity ∧
        D.kernelFeatureMapData.rkhsCharacterization ∧
        D.kernelFeatureMapData.projectionNormCharacterization ∧
        D.kernelFeatureMapData.reproducingProperty :=
    Omega.CircleDimension.paper_cdim_kernel_rkhs_feature_map D.kernelFeatureMapData
  rcases hFeatureMap with ⟨hFeatureIdentity, hRKHS, _, hReproducing⟩
  have hFiniteRankKernel : D.finiteRankKernel :=
    D.deriveFiniteRankKernel D.explicitKernelFiniteRankSum_h
  exact ⟨hFiniteRankKernel, D.deriveFiniteRankRKHS hFiniteRankKernel hRKHS,
    D.deriveBoundaryScalarDiagonalRestriction
      D.boundaryScalarProfile_h hFeatureIdentity hReproducing⟩

end Omega.TypedAddressBiaxialCompletion
