import Omega.TypedAddressBiaxialCompletion.PhaseLedgerTemplate

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing wrapper for the preferred minimal-instantiation phase/ledger split.
    prop:typed-address-biaxial-completion-preferred-minimal-instantiation-phase-ledger -/
theorem paper_typed_address_biaxial_completion_preferred_minimal_instantiation_phase_ledger
    (T : PhaseLedgerTemplate) :
    T.hasContinuousPhaseFactor ∧ T.hasTotallyDisconnectedLedgerFactor ∧
      T.hasPrimeLocalizedModel := by
  exact paper_typed_address_biaxial_completion_phase_ledger_template T

end Omega.TypedAddressBiaxialCompletion
