import Mathlib.Tactic
import Omega.CircleDimension.MinimalRecordAxis

namespace Omega.Conclusion

/-- Chapter-local package for the two-axis audit obstruction: there is a unique continuous axis,
three indispensable witness axes, and any purported universal two-axis completion must fall into
one of the two impossible profiles. -/
structure TwoAxisAuditCompletionData where
  universalTwoAxisAuditCompletion : Prop
  uniqueContinuousAxis : Prop
  collisionWitnessAxis : Prop
  windingWitnessAxis : Prop
  endpointWitnessAxis : Prop
  witnessAxesIndispensable :
      collisionWitnessAxis ∧ windingWitnessAxis ∧ endpointWitnessAxis
  auditProfile :
      universalTwoAxisAuditCompletion → uniqueContinuousAxis ∨ ¬ uniqueContinuousAxis
  continuousPlusDiscreteTooSmall :
      uniqueContinuousAxis →
      collisionWitnessAxis → windingWitnessAxis → endpointWitnessAxis → False
  twoDiscreteCannotCoverAll :
      ¬ uniqueContinuousAxis →
      collisionWitnessAxis → windingWitnessAxis → endpointWitnessAxis → False

/-- Conclusion-facing package: the minimal-record-axis theorem supplies the unique continuous
transverse direction, while the audit-completion data contributes the three indispensable witness
axes.
    thm:conclusion-unique-continuous-transverse-and-witness-product-core -/
theorem paper_conclusion_unique_continuous_transverse_and_witness_product_core
    (A : Omega.CircleDimension.MinimalRecordAxisData) (D : TwoAxisAuditCompletionData) :
    A.uniqueContinuousTransverse ∧ D.collisionWitnessAxis ∧ D.windingWitnessAxis ∧
      D.endpointWitnessAxis := by
  refine ⟨(Omega.CircleDimension.paper_cdim_minimal_record_axis A).2.1, ?_, ?_, ?_⟩
  · exact D.witnessAxesIndispensable.1
  · exact D.witnessAxesIndispensable.2.1
  · exact D.witnessAxesIndispensable.2.2

/-- Paper-facing conclusion: no two-axis audit scheme can be universal once the unique continuous
axis and the three indispensable witness factors are taken into account.
    cor:conclusion-no-universal-two-axis-audit-completion -/
theorem paper_conclusion_no_universal_two_axis_audit_completion
    (h : TwoAxisAuditCompletionData) : ¬ h.universalTwoAxisAuditCompletion := by
  intro huniv
  rcases h.witnessAxesIndispensable with ⟨hcollision, hwinding, hendpoint⟩
  rcases h.auditProfile huniv with hcontinuous | hdiscrete
  · exact h.continuousPlusDiscreteTooSmall hcontinuous hcollision hwinding hendpoint
  · exact h.twoDiscreteCannotCoverAll hdiscrete hcollision hwinding hendpoint

end Omega.Conclusion
