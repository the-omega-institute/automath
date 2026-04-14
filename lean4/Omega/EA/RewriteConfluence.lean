import Omega.EA.RewriteCore

namespace Omega.EA

open RewriteCore

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: the exact rewrite system is terminating and confluent,
    so every reduction path reaches the same normal form.
    thm:rewrite-confluence -/
theorem paper_projection_rewrite_confluence_seeds
    {W W₁ W₂ : RewriteCore.Word} (h₁ : RewriteCore.Reduces W W₁)
    (h₂ : RewriteCore.Reduces W W₂) :
    (∀ {A B : RewriteCore.Word}, RewriteCore.Step A B → B.length < A.length) ∧
      ∃ U, RewriteCore.Reduces W₁ U ∧ RewriteCore.Reduces W₂ U := by
  exact ⟨fun {_ _} h => RewriteCore.step_length_lt h, RewriteCore.confluent h₁ h₂⟩

end Omega.EA
