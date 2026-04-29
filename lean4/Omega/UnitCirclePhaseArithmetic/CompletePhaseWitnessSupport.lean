import Omega.TypedAddressBiaxialCompletion.FailureWitnessSupport

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:unit-circle-complete-phase-witness-support`. -/
theorem paper_unit_circle_complete_phase_witness_support
    (D : Omega.TypedAddressBiaxialCompletion.FailureWitnessSupportData) :
    D.nullReadout → D.witnessOnRecordAxis ∧ D.noNewContinuousAxis := by
  exact Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_witness_support D

end Omega.UnitCirclePhaseArithmetic
