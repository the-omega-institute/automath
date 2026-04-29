import Omega.Folding.BinFold
import Omega.GU.TerminalFoldbin6BoundaryPureF9Alias

open Omega.GU

namespace Omega.Folding

/-- Paper-facing package of the window-`6` BinFold multiplicity extrema, audited histogram,
and the pure-`F₉` boundary alias. -/
theorem paper_fold_bin_m6_fiber_hist :
    cBinFiberMin 6 = 2 ∧ cBinFiberMax 6 = 4 ∧ cBinFiberHist 6 2 = 8 ∧ cBinFiberHist 6 3 = 4 ∧
      cBinFiberHist 6 4 = 9 ∧
      terminalFoldbin6TailOffsets = {Nat.fib 8, Nat.fib 9, Nat.fib 10} ∧
      (∀ baseValue : Nat, terminalFoldbin6BoundaryAlias baseValue = {baseValue, baseValue + Nat.fib 9}) := by
  refine ⟨cBinFiberMin_six, cBinFiberMax_six, cBinFiberHist_6_2, cBinFiberHist_6_3,
    cBinFiberHist_6_4, ?_, ?_⟩
  · exact (paper_terminal_foldbin6_boundary_pure_f9_alias 0).1
  · intro baseValue
    exact (paper_terminal_foldbin6_boundary_pure_f9_alias baseValue).2.2

end Omega.Folding
