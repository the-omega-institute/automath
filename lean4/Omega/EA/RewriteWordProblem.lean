import Omega.EA.RewriteCore

namespace Omega.EA

open RewriteCore

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: two exact rewrite words have the same normal form exactly when they
    share a common reduct. This packages the decidable core of the word problem.
    cor:rewrite-word-problem -/
theorem paper_projection_rewrite_word_problem_seeds (W₁ W₂ : RewriteCore.Word) :
    RewriteCore.normalize W₁ = RewriteCore.normalize W₂ ↔
      ∃ U, RewriteCore.Reduces W₁ U ∧ RewriteCore.Reduces W₂ U := by
  constructor
  · intro h
    refine ⟨RewriteCore.normalize W₁, RewriteCore.reduces_to_normalize W₁, ?_⟩
    simpa [h] using RewriteCore.reduces_to_normalize W₂
  · rintro ⟨U, h₁, h₂⟩
    exact (RewriteCore.reduces_preserves_normalize h₁).trans
      (RewriteCore.reduces_preserves_normalize h₂).symm

end Omega.EA
