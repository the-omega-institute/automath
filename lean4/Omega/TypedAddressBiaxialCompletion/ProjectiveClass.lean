import Omega.TypedAddressBiaxialCompletion.PhaseResidual
import Omega.TypedAddressBiaxialCompletion.ProjectiveOrganization

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper: `cor:typed-address-biaxial-completion-projective-class`.
If the visible residual class is nontrivial, the visible phase cannot be globally trivialized. In
that case any gauge-invariant backend readout factors only through the projective quotient. -/
theorem paper_typed_address_biaxial_completion_projective_class
    {Lift Rep : Type} (S : Setoid Lift) (backend : Lift → Rep)
    (hbackend : ∀ a b : Lift, S.r a b → backend a = backend b)
    (hresidual : typedAddressVisibleResidualClass ≠ 0) :
    ¬ typedAddressVisiblePhaseTrivializable ∧
      ∃ backend' : Quotient S → Rep, backend = fun ℓ => backend' (Quotient.mk S ℓ) := by
  have hphase := paper_typed_address_biaxial_completion_phase_residual
  rcases hphase with ⟨_, htriv⟩
  refine ⟨?_, paper_typed_address_biaxial_completion_projective_organization S backend hbackend⟩
  intro hglobal
  exact hresidual (htriv.mpr hglobal)

end Omega.TypedAddressBiaxialCompletion
