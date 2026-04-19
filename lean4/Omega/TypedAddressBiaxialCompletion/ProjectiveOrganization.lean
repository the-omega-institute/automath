import Omega.CircleDimension.ProjectiveStateOrganization

namespace Omega.TypedAddressBiaxialCompletion

/-- Typed-address wrapper for the quotient-factorization theorem: any backend representation
constant on local gauge classes descends to the visible-state quotient.
    prop:typed-address-biaxial-completion-projective-organization -/
theorem paper_typed_address_biaxial_completion_projective_organization {Lift Rep : Type}
    (S : Setoid Lift) (backend : Lift → Rep)
    (hbackend : ∀ a b : Lift, S.r a b → backend a = backend b) :
    ∃ backend' : Quotient S → Rep, backend = fun ℓ => backend' (Quotient.mk S ℓ) := by
  exact Omega.CircleDimension.paper_cdim_projective_state_organization S backend hbackend

end Omega.TypedAddressBiaxialCompletion
