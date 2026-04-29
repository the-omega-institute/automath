import Omega.Folding.Rewrite

namespace Omega

namespace Rewrite

theorem reflTransGen_rankLex_le {a b : DigitCfg} (h : Relation.ReflTransGen Step a b) :
    rankLex b ≤ rankLex a := by
  induction h with
  | refl =>
      exact le_rfl
  | tail hab hStep ih =>
      exact le_trans (le_of_lt (step_rankLex hStep)) ih

end Rewrite

/-- Paper: `prop:potential-lexmin-zeckendorf`.
    The fold rewrite system has a unique irreducible descendant in each Fibonacci-value fiber, and
    that terminal Zeckendorf form minimizes the lexicographic potential `rankLex`. -/
theorem paper_fold_potential_lexmin_zeckendorf (a : Rewrite.DigitCfg) :
    ∃! b, Relation.ReflTransGen Rewrite.Step a b ∧ Rewrite.Irreducible b ∧
      ∀ c : Rewrite.DigitCfg, Rewrite.value c = Rewrite.value a → Rewrite.rankLex b ≤ Rewrite.rankLex c := by
  obtain ⟨b, hab, hIrrB⟩ := Rewrite.exists_irreducible_descendant a
  refine ⟨b, ?_, ?_⟩
  · refine ⟨hab, hIrrB, ?_⟩
    intro c hVal
    obtain ⟨d, hcd, hIrrD⟩ := Rewrite.exists_irreducible_descendant c
    have hValB : Rewrite.value b = Rewrite.value a := Rewrite.reflTransGen_value hab
    have hValD : Rewrite.value d = Rewrite.value a := by
      calc
        Rewrite.value d = Rewrite.value c := Rewrite.reflTransGen_value hcd
        _ = Rewrite.value a := hVal
    have hdb : d = b := Rewrite.irreducible_eq_of_value_eq hIrrD hIrrB (hValD.trans hValB.symm)
    simpa [hdb] using Rewrite.reflTransGen_rankLex_le hcd
  · intro c hc
    rcases hc with ⟨hac, hIrrC, _hMin⟩
    apply Rewrite.irreducible_eq_of_value_eq hIrrC hIrrB
    calc
      Rewrite.value c = Rewrite.value a := Rewrite.reflTransGen_value hac
      _ = Rewrite.value b := (Rewrite.reflTransGen_value hab).symm

/-- Paper: `prop:potential-lexmin-zeckendorf`.
    Label-preserving alias for the Zeckendorf lex-min reduction package. -/
theorem paper_potential_lexmin_zeckendorf (a : Rewrite.DigitCfg) :
    ∃! b, Relation.ReflTransGen Rewrite.Step a b ∧ Rewrite.Irreducible b ∧
      ∀ c : Rewrite.DigitCfg, Rewrite.value c = Rewrite.value a → Rewrite.rankLex b ≤ Rewrite.rankLex c :=
  paper_fold_potential_lexmin_zeckendorf a

end Omega
