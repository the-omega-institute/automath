import Omega.EA.RewriteCore

namespace Omega.EA

open RewriteCore

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: the exact rewrite system on `Z` and `E_n` words is locally confluent.
    lem:rewrite-local-confluence -/
theorem paper_projection_rewrite_local_confluence_seeds
    {W W₁ W₂ : RewriteCore.Word} (h₁ : RewriteCore.Step W W₁) (h₂ : RewriteCore.Step W W₂) :
    ∃ U, RewriteCore.Reduces W₁ U ∧ RewriteCore.Reduces W₂ U := by
  exact RewriteCore.step_locallyConfluent h₁ h₂

end Omega.EA
