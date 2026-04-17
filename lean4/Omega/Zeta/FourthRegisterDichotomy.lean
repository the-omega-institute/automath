import Omega.TypedAddressBiaxialCompletion.OffsliceDichotomy

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Xi-facing wrapper for the standard off-slice dichotomy: an off-slice assertion either lifts to
an explicit radial extension or collapses to a `NULL` witness, and the no-third-path clause
packages the exclusion of any extra continuous register.
    cor:xi-fourth-register-dichotomy -/
theorem paper_xi_fourth_register_dichotomy
    (offsliceAssertion explicitRadialExtension nullWitness noThirdPath : Prop)
    (hSplit : offsliceAssertion → explicitRadialExtension ∨ nullWitness)
    (hNoThird : offsliceAssertion → noThirdPath) :
    offsliceAssertion → (explicitRadialExtension ∨ nullWitness) ∧ noThirdPath := by
  intro hOffslice
  exact
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_offslice_dichotomy
      offsliceAssertion explicitRadialExtension nullWitness noThirdPath hSplit hNoThird hOffslice

end Omega.Zeta
