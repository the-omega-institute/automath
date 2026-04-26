import Mathlib.Tactic
import Omega.Zeta.DephysIdempotentMonadIProjection

namespace Omega.Zeta

/-- The projector lands in the fixed-point locus of the dephysicalized externalization. -/
def dephys_horizon_sufficiency_zero_knowledge_projector_to_fixedPoint
    {State Obs Val : Type*} (restrict : State → Obs → Val) (lift : (Obs → Val) → State)
    (hsection : ∀ σ, dephysExternalRestriction restrict (lift σ) = σ) :
    State → dephys_idempotent_monad_i_projection_fixedPoints restrict lift :=
  fun ρ =>
    ⟨dephys_idempotent_monad_i_projection_projector restrict lift ρ, by
      have hsec := hsection (dephysExternalRestriction restrict ρ)
      simpa [dephys_idempotent_monad_i_projection_projector, dephysExternalRestriction] using
        congrArg lift hsec⟩

lemma dephys_horizon_sufficiency_zero_knowledge_projector_preserves_externalization
    {State Obs Val : Type*} (restrict : State → Obs → Val) (lift : (Obs → Val) → State)
    (hsection : ∀ σ, dephysExternalRestriction restrict (lift σ) = σ) (ρ : State) :
    dephysExternalRestriction restrict
        (dephys_idempotent_monad_i_projection_projector restrict lift ρ) =
      dephysExternalRestriction restrict ρ := by
  simpa [dephys_idempotent_monad_i_projection_projector, dephysExternalRestriction] using
    hsection (dephysExternalRestriction restrict ρ)

lemma dephys_horizon_sufficiency_zero_knowledge_projector_to_fixedPoint_eq_self
    {State Obs Val : Type*} (restrict : State → Obs → Val) (lift : (Obs → Val) → State)
    (hsection : ∀ σ, dephysExternalRestriction restrict (lift σ) = σ)
    (σ : dephys_idempotent_monad_i_projection_fixedPoints restrict lift) :
    dephys_horizon_sufficiency_zero_knowledge_projector_to_fixedPoint
        restrict lift hsection σ.1 = σ := by
  apply Subtype.ext
  exact σ.2

/-- External invariance means the Boolean verifier depends only on the dephysicalized horizon
state, i.e. only on the fixed-point image of the projector. -/
def dephys_horizon_sufficiency_zero_knowledge_statement : Prop :=
  ∀ {State Obs Val : Type*} (restrict : State → Obs → Val) (lift : (Obs → Val) → State)
    (hsection : ∀ σ, dephysExternalRestriction restrict (lift σ) = σ) (V : State → Bool),
    (∀ ρ ρ' : State,
      dephysExternalRestriction restrict ρ =
        dephysExternalRestriction restrict ρ' → V ρ = V ρ') →
      ∃! v : dephys_idempotent_monad_i_projection_fixedPoints restrict lift → Bool,
        ∀ ρ : State,
          v (dephys_horizon_sufficiency_zero_knowledge_projector_to_fixedPoint
            restrict lift hsection ρ) = V ρ

/-- Paper label: `prop:dephys-horizon-sufficiency-zero-knowledge`. -/
theorem paper_dephys_horizon_sufficiency_zero_knowledge :
    dephys_horizon_sufficiency_zero_knowledge_statement := by
  intro State Obs Val restrict lift hsection V hV
  let v : dephys_idempotent_monad_i_projection_fixedPoints restrict lift → Bool := fun σ => V σ.1
  refine ⟨v, ?_, ?_⟩
  · intro ρ
    dsimp [v]
    exact hV _ _ <|
      dephys_horizon_sufficiency_zero_knowledge_projector_preserves_externalization
        restrict lift hsection ρ
  · intro w hw
    funext σ
    have hwσ := hw σ.1
    rw [dephys_horizon_sufficiency_zero_knowledge_projector_to_fixedPoint_eq_self
      restrict lift hsection σ] at hwσ
    simpa [v] using hwσ

end Omega.Zeta
