import Omega.TypedAddressBiaxialCompletion.FailureWitnessSupport
import Omega.TypedAddressBiaxialCompletion.OffsliceDichotomy

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local wrapper for the visible/`NULL` dichotomy: every protocol-internal off-slice
assertion either externalizes the mode axis or yields the finite `NULL` witness, and no third
branch survives the protocol bookkeeping.
    cor:typed-address-biaxial-completion-visible-null-dichotomy -/
theorem paper_typed_address_biaxial_completion_visible_null_dichotomy
    (offsliceAssertion explicitModeAxis nullFailureWitness noThirdPath : Prop)
    (hSplit : offsliceAssertion → explicitModeAxis ∨ nullFailureWitness)
    (hNoThird : offsliceAssertion → noThirdPath) :
    offsliceAssertion → (explicitModeAxis ∨ nullFailureWitness) ∧ noThirdPath := by
  exact paper_typed_address_biaxial_completion_offslice_dichotomy offsliceAssertion
    explicitModeAxis nullFailureWitness noThirdPath hSplit hNoThird

end Omega.TypedAddressBiaxialCompletion
