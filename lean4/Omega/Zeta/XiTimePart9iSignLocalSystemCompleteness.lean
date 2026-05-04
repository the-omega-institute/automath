import Mathlib.Tactic

namespace Omega.Zeta

universe u

/-- The two character classes available for a `d ≥ 3` finite symmetric monodromy factor. -/
inductive xi_time_part9i_sign_local_system_completeness_character_outcome where
  | xi_time_part9i_sign_local_system_completeness_trivial
  | xi_time_part9i_sign_local_system_completeness_sign

/-- Concrete data for the sign local-system completeness corollary.

The base loops are represented by the type `loop`.  The local system character factors through
the finite monodromy representation, and the supplied `d ≥ 3` classification says that this
factor is either the trivial Boolean character or the orientation character. -/
structure xi_time_part9i_sign_local_system_completeness_data where
  degree : ℕ
  degree_ge_three : 3 ≤ degree
  loop : Type u
  coverMonodromy : loop → Equiv.Perm (Fin degree)
  localSystemMonodromy : loop → Bool
  orientationLocalSystemMonodromy : loop → Bool
  character : Equiv.Perm (Fin degree) → Bool
  orientationCharacter : Equiv.Perm (Fin degree) → Bool
  factors_through_cover :
    ∀ γ : loop, localSystemMonodromy γ = character (coverMonodromy γ)
  orientation_factors_through_cover :
    ∀ γ : loop, orientationLocalSystemMonodromy γ = orientationCharacter (coverMonodromy γ)
  symmetric_two_character_classification :
    character = (fun _ => false) ∨ character = orientationCharacter

namespace xi_time_part9i_sign_local_system_completeness_data

/-- The local system is either trivial or equal to the orientation local system on all loops. -/
def is_trivial_or_orientation
    (D : xi_time_part9i_sign_local_system_completeness_data) : Prop :=
  (∀ γ : D.loop, D.localSystemMonodromy γ = false) ∨
    ∀ γ : D.loop, D.localSystemMonodromy γ = D.orientationLocalSystemMonodromy γ

end xi_time_part9i_sign_local_system_completeness_data

/-- Paper label: `cor:xi-time-part9i-sign-local-system-completeness`. -/
theorem paper_xi_time_part9i_sign_local_system_completeness
    (D : xi_time_part9i_sign_local_system_completeness_data) :
    D.is_trivial_or_orientation := by
  rcases D.symmetric_two_character_classification with htrivial | hsign
  · left
    intro γ
    rw [D.factors_through_cover γ, htrivial]
  · right
    intro γ
    rw [D.factors_through_cover γ, D.orientation_factors_through_cover γ, hsign]

end Omega.Zeta
