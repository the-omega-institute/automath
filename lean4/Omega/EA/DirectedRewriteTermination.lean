import Mathlib.Logic.Relation
import Omega.EA.RewriteTermination

namespace Omega.EA

set_option maxHeartbeats 400000 in
/-- Paper-facing directed rewrite termination package: the Zeckendorf digit rewrite system is
well founded, irreducible configurations are exactly the stable ones, and every configuration
admits a unique terminal irreducible descendant.
    prop:directed-rewrite-termination -/
theorem paper_directed_rewrite_termination :
    WellFounded (flip Omega.Rewrite.Step) ∧
      (∀ a : Omega.Rewrite.DigitCfg, Omega.Rewrite.Irreducible a ↔ Omega.Rewrite.StableCfg a) ∧
      (∀ a : Omega.Rewrite.DigitCfg, ∃! b : Omega.Rewrite.DigitCfg,
        Relation.ReflTransGen Omega.Rewrite.Step a b ∧ Omega.Rewrite.Irreducible b) := by
  obtain ⟨hTermination, hIrreducible, hUniqueTerminal⟩ :=
    paper_zeckendorf_rewrite_termination_seeds
  refine ⟨hTermination, hIrreducible, ?_⟩
  intro a
  obtain ⟨b, hab, hIrrB⟩ := Omega.Rewrite.exists_irreducible_descendant a
  refine ⟨b, ⟨hab, hIrrB⟩, ?_⟩
  intro c hc
  exact (hUniqueTerminal a b c hab hc.1 hIrrB hc.2).symm

end Omega.EA
