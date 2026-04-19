import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.CompletenessGapAudit
import Omega.TypedAddressBiaxialCompletion.UniqueContinuousTransversal

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete witness-support package for `NULL` readouts in the typed-address biaxial chapter.
The completeness-gap audit supplies the failure witness, while the existing minimal-record-axis
wrapper fixes the ambient record axis and the unique continuous transversal. -/
structure FailureWitnessSupportData where
  completenessGap : CompletenessGapAuditData
  recordAxis : Omega.CircleDimension.MinimalRecordAxisData

/-- The `NULL` readout under discussion. -/
def FailureWitnessSupportData.nullReadout (D : FailureWitnessSupportData) : Prop :=
  D.completenessGap.nullReadout

/-- Any legal failure witness lives on the already-audited record axis. -/
def FailureWitnessSupportData.witnessOnRecordAxis (D : FailureWitnessSupportData) : Prop :=
  D.completenessGap.modeStabilityCert ∧ D.recordAxis.initialObject

/-- The witness-support package does not create a fresh continuous direction. -/
def FailureWitnessSupportData.noNewContinuousAxis (D : FailureWitnessSupportData) : Prop :=
  D.recordAxis.uniqueContinuousTransverse

/-- Packaging of the witness-support statement: a `NULL` readout already carries the mode-stability
certificate from the completeness-gap audit, and the existing minimal-record-axis package forces
that witness onto the canonical record axis with no new continuous transversal.
    prop:typed-address-biaxial-completion-witness-support -/
theorem paper_typed_address_biaxial_completion_witness_support (D : FailureWitnessSupportData) :
    D.nullReadout -> D.witnessOnRecordAxis ∧ D.noNewContinuousAxis := by
  intro hNull
  have hGap :
      D.completenessGap.modeStabilityCert ∧
        D.completenessGap.residueQuotaCert ∧ D.completenessGap.endpointResolutionGate :=
    paper_typed_address_biaxial_completion_completeness_gap_audit D.completenessGap hNull
  have hAxis :
      D.recordAxis.initialObject ∧
        D.recordAxis.uniqueContinuousTransverse ∧ D.recordAxis.orthogonalExternalization :=
    Omega.CircleDimension.paper_cdim_minimal_record_axis D.recordAxis
  have hTrans :
      D.recordAxis.uniqueContinuousTransverse :=
    paper_typed_address_biaxial_completion_unique_continuous_transversal D.recordAxis
  exact ⟨⟨hGap.1, hAxis.1⟩, hTrans⟩

end Omega.TypedAddressBiaxialCompletion
