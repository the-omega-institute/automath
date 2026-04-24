import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic
import Omega.GU.TerminalFoldbinSaturationDiophantine

namespace Omega.GU

/-- In the chapter-local saturation model, the only exact solutions of
`terminalFoldbinAlternatingTailCutoff m = 2^m - 1` occur in the finite base window `m ≤ 1`; hence
the exceptional exact-saturation locus is finite.
    cor:terminal-foldbin-finite-saturation -/
theorem paper_terminal_foldbin_finite_saturation :
    (∀ m,
      saturation_point m ∧ terminalFoldbinAlternatingTailCutoff m = 2 ^ m - 1 → m ≤ 1) ∧
      {m : ℕ | saturation_point m ∧ terminalFoldbinAlternatingTailCutoff m = 2 ^ m - 1}.Finite := by
  have hsmall :
      ∀ m,
        saturation_point m ∧ terminalFoldbinAlternatingTailCutoff m = 2 ^ m - 1 → m ≤ 1 := by
    intro m hm
    rcases hm with ⟨hsat, heq⟩
    by_contra hgt
    have hm2 : 2 ≤ m := by omega
    have hineq :
        terminalFoldbinAlternatingTailCutoff m ≤ 2 ^ m - 1 :=
      (paper_terminal_foldbin_saturation_diophantine m hm2).2.2.mp hsat
    by_cases hEven : Even m
    · have hpow : 1 < 2 ^ m := Nat.one_lt_two_pow (show m ≠ 0 by omega)
      have heq' : 0 = 2 ^ m - 1 := by
        simpa [terminalFoldbinAlternatingTailCutoff, hEven] using heq
      omega
    · have hpow4 : 4 ≤ 2 ^ m := by
        simpa using (Nat.pow_le_pow_right (show 0 < 2 by decide) hm2)
      have heq' : 1 = 2 ^ m - 1 := by
        simpa [terminalFoldbinAlternatingTailCutoff, hEven] using heq
      omega
  refine ⟨hsmall, Set.Finite.subset (Set.finite_le_nat 1) ?_⟩
  intro m hm
  exact hsmall m hm

end Omega.GU
