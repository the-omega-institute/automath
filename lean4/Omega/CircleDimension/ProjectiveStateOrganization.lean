import Mathlib.Tactic

namespace Omega.CircleDimension

/-- A backend representation that is constant on local-gauge equivalence classes descends to the
projective quotient. -/
theorem paper_cdim_projective_state_organization {Lift Rep : Type} (S : Setoid Lift)
    (backend : Lift → Rep) (hbackend : ∀ a b : Lift, S.r a b → backend a = backend b) :
    ∃ backend' : Quotient S → Rep, backend = fun ℓ => backend' (Quotient.mk S ℓ) := by
  refine ⟨Quotient.lift backend (fun a b hab => hbackend a b hab), ?_⟩
  funext ℓ
  rfl

end Omega.CircleDimension
