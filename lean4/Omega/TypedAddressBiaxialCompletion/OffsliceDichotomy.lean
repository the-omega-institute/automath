import Omega.TypedAddressBiaxialCompletion.ExplicitLifting

namespace Omega.TypedAddressBiaxialCompletion

set_option maxHeartbeats 400000 in
/-- Chapter-local wrapper for the protocol-internal off-slice dichotomy: every off-slice event
    either carries an explicit mode-axis extension or degenerates to a finite `NULL` witness, and
    no third branch remains available inside the completion protocol.
    cor:typed-address-biaxial-completion-offslice-dichotomy -/
theorem paper_typed_address_biaxial_completion_offslice_dichotomy
    (offsliceAssertion explicitModeAxis nullFailureWitness noThirdPath : Prop)
    (hSplit : offsliceAssertion -> explicitModeAxis ∨ nullFailureWitness)
    (hNoThird : offsliceAssertion -> noThirdPath) :
    offsliceAssertion -> (explicitModeAxis ∨ nullFailureWitness) ∧ noThirdPath := by
  intro hOffslice
  exact ⟨hSplit hOffslice, hNoThird hOffslice⟩

end Omega.TypedAddressBiaxialCompletion
