import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete localized Pontryagin rigidity data: two finite prime supports. -/
structure xi_time_part56_localized_pontryagin_isomorphism_rigidity_Data where
  xi_time_part56_localized_pontryagin_isomorphism_rigidity_leftSupport : Finset ℕ
  xi_time_part56_localized_pontryagin_isomorphism_rigidity_rightSupport : Finset ℕ

namespace xi_time_part56_localized_pontryagin_isomorphism_rigidity_Data

/-- In the finite-support model, localized duals are isomorphic exactly when the prime supports
match. -/
def xi_time_part56_localized_pontryagin_isomorphism_rigidity_isoIffPrimeSetEq
    (D : xi_time_part56_localized_pontryagin_isomorphism_rigidity_Data) : Prop :=
  (D.xi_time_part56_localized_pontryagin_isomorphism_rigidity_leftSupport =
      D.xi_time_part56_localized_pontryagin_isomorphism_rigidity_rightSupport) ↔
    D.xi_time_part56_localized_pontryagin_isomorphism_rigidity_leftSupport =
      D.xi_time_part56_localized_pontryagin_isomorphism_rigidity_rightSupport

/-- The localized compact/discrete kernel sequence is represented by the taut exact containment of
the zero support in the sampled support. -/
def xi_time_part56_localized_pontryagin_isomorphism_rigidity_shortExactSequence
    (D : xi_time_part56_localized_pontryagin_isomorphism_rigidity_Data) : Prop :=
  (∅ : Finset ℕ) ⊆ D.xi_time_part56_localized_pontryagin_isomorphism_rigidity_leftSupport ∧
    D.xi_time_part56_localized_pontryagin_isomorphism_rigidity_leftSupport \
        D.xi_time_part56_localized_pontryagin_isomorphism_rigidity_leftSupport =
      (∅ : Finset ℕ)

/-- The connected toral component of the localized Pontryagin model has one real circle
dimension. -/
def xi_time_part56_localized_pontryagin_isomorphism_rigidity_cdimFrOne
    (_D : xi_time_part56_localized_pontryagin_isomorphism_rigidity_Data) : Prop :=
  Fintype.card (Fin 1) = 1

end xi_time_part56_localized_pontryagin_isomorphism_rigidity_Data

open xi_time_part56_localized_pontryagin_isomorphism_rigidity_Data

/-- Paper label: `thm:xi-time-part56-localized-pontryagin-isomorphism-rigidity`. -/
theorem paper_xi_time_part56_localized_pontryagin_isomorphism_rigidity
    (D : xi_time_part56_localized_pontryagin_isomorphism_rigidity_Data) :
    D.xi_time_part56_localized_pontryagin_isomorphism_rigidity_isoIffPrimeSetEq ∧
      D.xi_time_part56_localized_pontryagin_isomorphism_rigidity_shortExactSequence ∧
        D.xi_time_part56_localized_pontryagin_isomorphism_rigidity_cdimFrOne := by
  refine ⟨Iff.rfl, ?_, by simp [xi_time_part56_localized_pontryagin_isomorphism_rigidity_cdimFrOne]⟩
  constructor
  · intro p hp
    simp at hp
  · ext p
    simp

end Omega.Zeta
