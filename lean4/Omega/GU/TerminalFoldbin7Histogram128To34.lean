import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.Folding.FiberArithmetic

namespace Omega.GU

open Omega

/-- The window-`7` BinFold histogram has multiplicities `3, 4, 5`, totals `34` stable states,
and resolves the full `128` dyadic mass.
    thm:terminal-foldbin7-128-to-34-hist -/
theorem paper_terminal_foldbin7_128_to_34_hist :
    cBinFiberHist 7 3 = 13 ∧ cBinFiberHist 7 4 = 16 ∧ cBinFiberHist 7 5 = 5 ∧
    Fintype.card (X 7) = 34 ∧
    cBinFiberHist 7 3 * 3 + cBinFiberHist 7 4 * 4 + cBinFiberHist 7 5 * 5 = 128 := by
  refine ⟨cBinFiberHist_7_3, cBinFiberHist_7_4, cBinFiberHist_7_5, X.card_X_seven,
    window7_histogram_fiber_sum⟩

end Omega.GU
