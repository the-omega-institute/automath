import Omega.CircleDimension.ProjectiveStateOrganization
import Omega.CircleDimension.VisiblePhaseResidualTriviality

namespace Omega.CircleDimension

/-- Nontrivial visible residual class obstructs global visible-phase trivialization, while any
gauge-invariant backend still factors through the projective quotient. -/
theorem paper_cdim_visible_state_projectivization {Lift Rep : Type} (S : Setoid Lift)
    (backend : Lift → Rep) (hbackend : ∀ a b : Lift, S.r a b → backend a = backend b)
    (hresidual : visible_residual_class ≠ 0) :
    ¬ visible_phase_trivializable ∧
      ∃ backend' : Quotient S → Rep, backend = fun ℓ => backend' (Quotient.mk S ℓ) := by
  refine ⟨?_, paper_cdim_projective_state_organization S backend hbackend⟩
  intro htriv
  exact hresidual (paper_cdim_visible_phase_residual_triviality.2.mpr htriv)

end Omega.CircleDimension
