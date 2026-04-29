import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Omega.Zeta.DephysicalizedHorizonQuotientDataStructure

namespace Omega.Zeta

/-- The dephysicalized projector obtained by lifting the external restriction back to the bulk. -/
def dephys_idempotent_monad_i_projection_projector {State Obs Val : Type*}
    (restrict : State → Obs → Val) (lift : (Obs → Val) → State) : State → State :=
  fun ρ => lift (dephysExternalRestriction restrict ρ)

/-- Fixed points of the dephysicalized projector. -/
def dephys_idempotent_monad_i_projection_fixedPoints {State Obs Val : Type*}
    (restrict : State → Obs → Val) (lift : (Obs → Val) → State) : Set State :=
  {ρ | dephys_idempotent_monad_i_projection_projector restrict lift ρ = ρ}

/-- Relative-entropy Pythagoras package for the dephysicalized projector. -/
def dephys_idempotent_monad_i_projection_relativeEntropyPythagoras {State Obs Val : Type*}
    (family : Set State) (restrict : State → Obs → Val) (lift : (Obs → Val) → State)
    (relativeEntropyBulk : State → State → ℝ)
    (relativeEntropyExt : (Obs → Val) → (Obs → Val) → ℝ) : Prop :=
  ∀ ρ ∈ family, ∀ σ ∈ family,
    relativeEntropyBulk ρ σ =
      relativeEntropyExt (dephysExternalRestriction restrict ρ)
          (dephysExternalRestriction restrict σ) +
        relativeEntropyBulk ρ
          (dephys_idempotent_monad_i_projection_projector restrict lift σ)

/-- Concrete statement for the dephysicalized idempotent-monad I-projection package. -/
def dephys_idempotent_monad_i_projection_statement {State Obs Val : Type*}
    (family : Set State) (restrict : State → Obs → Val) (lift : (Obs → Val) → State)
    (relativeEntropyBulk : State → State → ℝ)
    (relativeEntropyExt : (Obs → Val) → (Obs → Val) → ℝ) : Prop :=
  (∀ ρ,
      dephys_idempotent_monad_i_projection_projector restrict lift
          (dephys_idempotent_monad_i_projection_projector restrict lift ρ) =
        dephys_idempotent_monad_i_projection_projector restrict lift ρ) ∧
    (∀ ρ,
      ρ ∈ dephys_idempotent_monad_i_projection_fixedPoints restrict lift ↔
        dephys_idempotent_monad_i_projection_projector restrict lift ρ = ρ) ∧
    (∀ ρ,
      dephysExternalEquivalent restrict ρ
        (dephys_idempotent_monad_i_projection_projector restrict lift ρ)) ∧
    (∀ ρ ρ',
      dephysExternalEquivalent restrict ρ ρ' →
        dephys_idempotent_monad_i_projection_projector restrict lift ρ =
          dephys_idempotent_monad_i_projection_projector restrict lift ρ') ∧
    dephys_idempotent_monad_i_projection_relativeEntropyPythagoras
      family restrict lift relativeEntropyBulk relativeEntropyExt ∧
    ((∃ R : (Obs → Val) → State, ∀ ρ ∈ family, R (dephysExternalRestriction restrict ρ) = ρ) ↔
      (∀ ρ ∈ family, ∀ σ ∈ family,
        relativeEntropyBulk ρ σ =
          relativeEntropyExt (dephysExternalRestriction restrict ρ)
              (dephysExternalRestriction restrict σ))) ∧
    ((∃ R : (Obs → Val) → State, ∀ ρ ∈ family, R (dephysExternalRestriction restrict ρ) = ρ) ↔
      (∀ ρ ∈ family,
        dephys_idempotent_monad_i_projection_projector restrict lift ρ = ρ))

/-- Paper label: `thm:dephys-idempotent-monad-i-projection`. The lift of the externalization map
is an idempotent projector, its fixed points are the recovered states, quotient-equivalent states
have the same projector image, and the Petz sufficiency package identifies the I-projection
criterion with relative-entropy faithfulness and recoverability. -/
theorem paper_dephys_idempotent_monad_i_projection {State Obs Val : Type*}
    (family : Set State) (restrict : State → Obs → Val) (lift : (Obs → Val) → State)
    (relativeEntropyBulk : State → State → ℝ)
    (relativeEntropyExt : (Obs → Val) → (Obs → Val) → ℝ)
    (hsection : ∀ σ, dephysExternalRestriction restrict (lift σ) = σ)
    (hpythagoras :
      dephys_idempotent_monad_i_projection_relativeEntropyPythagoras
        family restrict lift relativeEntropyBulk relativeEntropyExt)
    (hsuff_to_entropy :
      (∃ R : (Obs → Val) → State, ∀ ρ ∈ family, R (dephysExternalRestriction restrict ρ) = ρ) →
        (∀ ρ ∈ family, ∀ σ ∈ family,
          relativeEntropyBulk ρ σ =
            relativeEntropyExt (dephysExternalRestriction restrict ρ)
              (dephysExternalRestriction restrict σ)))
    (hentropy_to_suff :
      (∀ ρ ∈ family, ∀ σ ∈ family,
        relativeEntropyBulk ρ σ =
          relativeEntropyExt (dephysExternalRestriction restrict ρ)
            (dephysExternalRestriction restrict σ)) →
        (∃ R : (Obs → Val) → State, ∀ ρ ∈ family, R (dephysExternalRestriction restrict ρ) = ρ))
    (hentropy_to_recover :
      (∀ ρ ∈ family, ∀ σ ∈ family,
        relativeEntropyBulk ρ σ =
          relativeEntropyExt (dephysExternalRestriction restrict ρ)
            (dephysExternalRestriction restrict σ)) →
        (∀ ρ ∈ family,
          dephys_idempotent_monad_i_projection_projector restrict lift ρ = ρ))
    (hrecover_to_suff :
      (∀ ρ ∈ family,
        dephys_idempotent_monad_i_projection_projector restrict lift ρ = ρ) →
        (∃ R : (Obs → Val) → State, ∀ ρ ∈ family, R (dephysExternalRestriction restrict ρ) = ρ)) :
    dephys_idempotent_monad_i_projection_statement
      family restrict lift relativeEntropyBulk relativeEntropyExt := by
  refine ⟨?_, ?_, ?_, ?_, hpythagoras, ?_, ?_⟩
  · intro ρ
    have hsec := hsection (dephysExternalRestriction restrict ρ)
    simpa [dephys_idempotent_monad_i_projection_projector, dephysExternalRestriction] using
      congrArg lift hsec
  · intro ρ
    rfl
  · intro ρ A
    have hsec := hsection (dephysExternalRestriction restrict ρ)
    simpa [dephys_idempotent_monad_i_projection_projector, dephysExternalRestriction] using
      (congrFun hsec A).symm
  · intro ρ ρ' hEq
    have hquot :
        dephysExternalRestriction restrict ρ = dephysExternalRestriction restrict ρ' :=
      (paper_dephys_zero_knowledge_quotient_factorization restrict).2 ρ ρ' hEq
    simpa [dephys_idempotent_monad_i_projection_projector, dephysExternalRestriction] using
      congrArg lift hquot
  · constructor
    · exact hsuff_to_entropy
    · exact hentropy_to_suff
  · constructor
    · intro hsuff ρ hρ
      exact hentropy_to_recover (hsuff_to_entropy hsuff) ρ hρ
    · exact hrecover_to_suff

end Omega.Zeta
