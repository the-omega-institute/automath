import Omega.EA.ProjectionWordNormalForm

namespace Omega.EA

open RewriteCore

private lemma normalize_idempotent (W : Word) : normalize (normalize W) = normalize W := by
  exact (reduces_preserves_normalize (reduces_to_normalize W)).symm

/-- Paper label: `prop:projection-word-rewrite`.
The two basic cancellation laws for the rewrite core imply that normalization is idempotent,
and its image is exactly the fixed-point locus. -/
theorem paper_projection_word_rewrite (m : ℕ) :
    (∀ W : Word, normalize (Letter.Z :: Letter.Z :: W) = normalize (Letter.Z :: W)) ∧
      (∀ W : Word, normalize (Letter.E m :: Letter.E m :: W) = normalize (Letter.E m :: W)) ∧
      (∀ W : Word, normalize (normalize W) = normalize W) ∧
      (∀ V : Word, (∃ W : Word, normalize W = V) ↔ normalize V = V) := by
  refine ⟨?_, ?_, normalize_idempotent, ?_⟩
  · intro W
    simp [normalize_cons, push_z_z]
  · intro W
    simp [normalize_cons, push_e_e]
  · intro V
    constructor
    · rintro ⟨W, rfl⟩
      exact normalize_idempotent W
    · intro hV
      exact ⟨V, hV⟩

end Omega.EA
