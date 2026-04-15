import Mathlib.Logic.Relation
import Omega.Folding.Rewrite

namespace Omega.EA

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: the Zeckendorf digit rewrite system is strongly terminating, its
    irreducible configurations are exactly the admissible ones, and terminal irreducibles are
    unique.
    prop:rewrite-termination -/
theorem paper_zeckendorf_rewrite_termination_seeds :
    WellFounded (flip Omega.Rewrite.Step) ∧
      (∀ a : Omega.Rewrite.DigitCfg, Omega.Rewrite.Irreducible a ↔ Omega.Rewrite.StableCfg a) ∧
      (∀ a b c : Omega.Rewrite.DigitCfg,
        Relation.ReflTransGen Omega.Rewrite.Step a b →
          Relation.ReflTransGen Omega.Rewrite.Step a c →
          Omega.Rewrite.Irreducible b →
          Omega.Rewrite.Irreducible c →
          b = c) := by
  refine ⟨Omega.Rewrite.step_stronglyTerminating, fun a => Omega.Rewrite.irreducible_iff_stableCfg,
    ?_⟩
  intro a b c hab hac hIrrB hIrrC
  exact Omega.Rewrite.irreducible_terminal_unique_unbounded hab hac hIrrB hIrrC

end Omega.EA
