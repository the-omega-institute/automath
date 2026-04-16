import Mathlib.Tactic

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
