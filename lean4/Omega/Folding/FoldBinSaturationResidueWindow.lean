import Mathlib.Tactic
import Omega.Folding.FoldbinSaturationSectorThreshold

namespace Omega.Folding

/-- Concrete residue-window restatement of the existing saturation-sector criterion. The tail
length is `K(m) - m = m`, so the maximal tail contribution is `F_{m+2} - 1`. -/
def fold_bin_saturation_residue_window_statement (m : ℕ) : Prop :=
  foldBinDigitTailLength m = m ∧
    foldbinSMax m = Nat.fib (m + 2) - 1 ∧
    (2 ≤ m →
      (∀ w : Omega.X m, foldbinSaturatesUpperBound m w ↔
        Omega.get w.1 (m - 1) = false ∧
          Omega.stableValue w + (Nat.fib (m + 2) - 1) ≤ 2 ^ m - 1) ∧
      (Set.Nonempty (foldbinSaturationSector m) ↔ Nat.fib (m + 2) - 1 ≤ 2 ^ m - 1) ∧
      (∀ w : Omega.X m, Omega.get w.1 (m - 1) = true → ¬ foldbinSaturatesUpperBound m w) ∧
      (∀ w : Omega.X m, 2 ^ m - 1 < Omega.stableValue w + (Nat.fib (m + 2) - 1) →
        ¬ foldbinSaturatesUpperBound m w))

/-- Paper label: `cor:fold-bin-saturation-residue-window`. -/
theorem paper_fold_bin_saturation_residue_window (m : ℕ) :
    fold_bin_saturation_residue_window_statement m := by
  refine ⟨foldBinDigitTailLength_eq m, ?_, ?_⟩
  · simp [foldbinSMax, foldBinDigitTailLength_eq]
  · intro hm
    simpa [foldbinSMax, foldBinDigitTailLength_eq, foldbinSaturatesUpperBound] using
      paper_foldbin_saturation_sector_threshold m hm

end Omega.Folding
