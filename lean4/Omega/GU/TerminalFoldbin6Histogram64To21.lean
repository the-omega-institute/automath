import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.Folding.FiberArithmetic

namespace Omega.GU

/-- Paper-facing wrapper for the exact `m = 6` BinFold histogram, the certified stable-word count
`|X₆| = 21`, and the weighted fiber-count check `64 = 8·2 + 4·3 + 9·4`.
    thm:terminal-foldbin6-64-to-21-hist -/
theorem paper_terminal_foldbin6_64_to_21_hist :
    cBinFiberHist 6 0 = 0 ∧ cBinFiberHist 6 1 = 0 ∧ cBinFiberHist 6 2 = 8 ∧
      cBinFiberHist 6 3 = 4 ∧ cBinFiberHist 6 4 = 9 ∧ cBinFiberHist 6 5 = 0 ∧
      Fintype.card (X 6) = 21 ∧
      cBinFiberHist 6 2 * 2 + cBinFiberHist 6 3 * 3 + cBinFiberHist 6 4 * 4 = 64 := by
  refine ⟨cBinFiberHist_6_0, cBinFiberHist_6_1, cBinFiberHist_6_2, cBinFiberHist_6_3,
    cBinFiberHist_6_4, cBinFiberHist_6_5, X.card_X_six, ?_⟩
  rw [cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]

end Omega.GU
