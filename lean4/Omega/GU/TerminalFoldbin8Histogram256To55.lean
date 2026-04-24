import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.Folding.FiberArithmetic

namespace Omega.GU

open Omega

/-- The window-`8` BinFold histogram has multiplicities `3, 5, 6`, totals `55` stable states,
and resolves the full `256` dyadic mass.
    thm:terminal-foldbin8-256-to-55-hist -/
theorem paper_terminal_foldbin8_256_to_55_hist :
    cBinFiberHist 8 3 = 21 ∧ cBinFiberHist 8 5 = 11 ∧ cBinFiberHist 8 6 = 23 ∧
    Fintype.card (X 8) = 55 ∧
    cBinFiberHist 8 3 * 3 + cBinFiberHist 8 5 * 5 + cBinFiberHist 8 6 * 6 = 256 := by
  refine ⟨cBinFiberHist_8_3, cBinFiberHist_8_5, cBinFiberHist_8_6, X.card_X_eight,
    window8_histogram_fiber_sum⟩

end Omega.GU
