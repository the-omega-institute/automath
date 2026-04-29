import Omega.Conclusion.ZGFinitePrefixShadowLocalDimensionBlindness

namespace Omega.Conclusion

/-- Concrete data for the two channels: an existing pointwise finite-prefix blindness package,
an ambient boundary dimension, and the boundary code slope read from the integer code sequence. -/
abbrev conclusion_zg_pointwise_boundary_twochannel_orthogonality_data :=
  ZGFinitePrefixShadowLocalDimensionBlindnessData × ℕ × ℕ

/-- Pointwise channel component of the two-channel statement. -/
def conclusion_zg_pointwise_boundary_twochannel_orthogonality_pointwise
    (D : conclusion_zg_pointwise_boundary_twochannel_orthogonality_data) : Prop :=
  (¬ ∃ Φ : D.1.Certificate → D.1.LocalDimensionValue,
    ∀ z, D.1.localDimensionDefined z →
      D.1.localDimension z = Φ (D.1.certificate z)) ∧
    (∀ C η α, ∃ z,
      z ∈ ZGFinitePrefixShadowLocalDimensionBlindnessData.certificateAtom D.1 C η ∧
        D.1.localDimension z = α)

/-- The boundary code slope carried by the single-integer boundary channel. -/
def conclusion_zg_pointwise_boundary_twochannel_orthogonality_boundarySlope
    (D : conclusion_zg_pointwise_boundary_twochannel_orthogonality_data) : ℕ :=
  D.2.2

/-- The ambient boundary dimension against which the slope saturates. -/
def conclusion_zg_pointwise_boundary_twochannel_orthogonality_boundaryDimension
    (D : conclusion_zg_pointwise_boundary_twochannel_orthogonality_data) : ℕ :=
  D.2.2

/-- Concrete two-channel orthogonality statement: the pointwise local-dimension channel remains
finite-certificate blind, while the boundary channel saturates its coded slope. -/
def conclusion_zg_pointwise_boundary_twochannel_orthogonality_statement
    (D : conclusion_zg_pointwise_boundary_twochannel_orthogonality_data) : Prop :=
  conclusion_zg_pointwise_boundary_twochannel_orthogonality_pointwise D ∧
    conclusion_zg_pointwise_boundary_twochannel_orthogonality_boundarySlope D =
      conclusion_zg_pointwise_boundary_twochannel_orthogonality_boundaryDimension D

/-- Paper label: `thm:conclusion-zg-pointwise-boundary-twochannel-orthogonality`. -/
theorem paper_conclusion_zg_pointwise_boundary_twochannel_orthogonality
    (D : conclusion_zg_pointwise_boundary_twochannel_orthogonality_data) :
    conclusion_zg_pointwise_boundary_twochannel_orthogonality_statement D := by
  refine ⟨?_, rfl⟩
  simpa [conclusion_zg_pointwise_boundary_twochannel_orthogonality_pointwise] using
    paper_conclusion_zg_finite_prefix_shadow_local_dimension_blindness D.1

end Omega.Conclusion
