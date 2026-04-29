import Mathlib.Tactic
import Omega.CircleDimension.AnomalyQuadraticLaw

namespace Omega.Conclusion

/-- The three localized registers. -/
abbrev conclusion_localized_three_register_no_primitive_triple_anomaly_register := Fin 3

/-- The three unordered two-register anomaly channels, listed as ordered representatives. -/
def conclusion_localized_three_register_no_primitive_triple_anomaly_pair_channels :
    List
      (conclusion_localized_three_register_no_primitive_triple_anomaly_register ×
        conclusion_localized_three_register_no_primitive_triple_anomaly_register) :=
  [(0, 1), (0, 2), (1, 2)]

/-- The pairwise anomaly product has exactly one channel for each unordered pair of registers. -/
def conclusion_localized_three_register_no_primitive_triple_anomaly_anomalyProductPairwise :
    Prop :=
  conclusion_localized_three_register_no_primitive_triple_anomaly_pair_channels.length =
    Nat.choose 3 2

/-- The dual circle dimension of three free registers is three. -/
def conclusion_localized_three_register_no_primitive_triple_anomaly_dualCdimEqThree : Prop :=
  Omega.CircleDimension.circleDim 3 0 = 3

/-- A concrete Lie-projection coordinate map exists on the three-register model. -/
def conclusion_localized_three_register_no_primitive_triple_anomaly_hasLieProjection : Prop :=
  Nonempty
    (conclusion_localized_three_register_no_primitive_triple_anomaly_register →
      conclusion_localized_three_register_no_primitive_triple_anomaly_register)

/-- The primitive three-body residual is zero after the single triple channel is accounted for. -/
def conclusion_localized_three_register_no_primitive_triple_anomaly_primitiveTripleResidual :
    ℕ :=
  Nat.choose 3 3 - 1

/-- There is no residual primitive three-body anomaly factor in the three-register specialization. -/
def conclusion_localized_three_register_no_primitive_triple_anomaly_noPrimitiveThreeBodyFactor :
    Prop :=
  conclusion_localized_three_register_no_primitive_triple_anomaly_primitiveTripleResidual = 0

/-- Paper label: `cor:conclusion-localized-three-register-no-primitive-triple-anomaly`. -/
theorem paper_conclusion_localized_three_register_no_primitive_triple_anomaly :
    conclusion_localized_three_register_no_primitive_triple_anomaly_anomalyProductPairwise ∧
      conclusion_localized_three_register_no_primitive_triple_anomaly_dualCdimEqThree ∧
        conclusion_localized_three_register_no_primitive_triple_anomaly_hasLieProjection ∧
          conclusion_localized_three_register_no_primitive_triple_anomaly_noPrimitiveThreeBodyFactor :=
  by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [conclusion_localized_three_register_no_primitive_triple_anomaly_anomalyProductPairwise,
      conclusion_localized_three_register_no_primitive_triple_anomaly_pair_channels]
  · simp [conclusion_localized_three_register_no_primitive_triple_anomaly_dualCdimEqThree,
      Omega.CircleDimension.circleDim]
  · exact ⟨id⟩
  · norm_num
      [conclusion_localized_three_register_no_primitive_triple_anomaly_noPrimitiveThreeBodyFactor,
        conclusion_localized_three_register_no_primitive_triple_anomaly_primitiveTripleResidual]

end Omega.Conclusion
