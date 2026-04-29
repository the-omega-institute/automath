import Omega.TypedAddressBiaxialCompletion.ComovingPronyThreshold

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper-facing unit-circle restatement of the typed-address Prony-threshold window lengths.
    thm:unit-circle-comoving-prony-threshold -/
theorem paper_unit_circle_comoving_prony_threshold
    (D : Omega.TypedAddressBiaxialCompletion.ComovingPronyThresholdData) :
    D.rankDetectionWindow = 2 * D.kappa - 1 ∧ D.exactRecoveryWindow = 2 * D.kappa := by
  simpa using
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_prony_threshold
      D

end Omega.UnitCirclePhaseArithmetic
