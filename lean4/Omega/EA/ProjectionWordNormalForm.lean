import Omega.EA.RewriteCore

namespace Omega.EA

theorem paper_projection_word_normal_form (W₁ W₂ : RewriteCore.Word) :
    (∃ U, RewriteCore.Reduces W₁ U ∧ RewriteCore.Reduces W₂ U) ↔
      RewriteCore.normalize W₁ = RewriteCore.normalize W₂ := by
  constructor
  · rintro ⟨U, h₁, h₂⟩
    exact (RewriteCore.reduces_preserves_normalize h₁).trans
      (RewriteCore.reduces_preserves_normalize h₂).symm
  · intro h
    refine ⟨RewriteCore.normalize W₁, RewriteCore.reduces_to_normalize W₁, ?_⟩
    simpa [h] using RewriteCore.reduces_to_normalize W₂

end Omega.EA
