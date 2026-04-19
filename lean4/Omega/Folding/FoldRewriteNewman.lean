import Omega.Folding.Rewrite

namespace Omega

/-- Paper-facing Newman-style wrapper for the fold rewrite system: every digit configuration has
an irreducible descendant, and that irreducible terminal object is unique among all descendants
reachable by the rewrite relation.
    prop:fold-rewrite-newman -/
theorem paper_fold_rewrite_newman (a : Omega.Rewrite.DigitCfg) :
    ∃ b, Relation.ReflTransGen Omega.Rewrite.Step a b ∧ Omega.Rewrite.Irreducible b ∧
      (∀ c, Relation.ReflTransGen Omega.Rewrite.Step a c → Omega.Rewrite.Irreducible c → c = b) := by
  obtain ⟨b, hab, hIrrB⟩ := Omega.Rewrite.exists_irreducible_descendant a
  refine ⟨b, hab, hIrrB, ?_⟩
  intro c hac hIrrC
  exact (Omega.Rewrite.irreducible_terminal_unique_unbounded hab hac hIrrB hIrrC).symm

end Omega
