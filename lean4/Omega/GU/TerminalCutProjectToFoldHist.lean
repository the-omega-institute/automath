import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6Histogram64To21
import Omega.GU.Window6RankGap

namespace Omega.GU

/-- The audited window-6 fold histogram: this is the concrete finite readout through the stable
language `X_6`. -/
def terminalCutProjectFoldHistogramFactors : Prop :=
  cBinFiberHist 6 0 = 0 ∧
    cBinFiberHist 6 1 = 0 ∧
    cBinFiberHist 6 2 = 8 ∧
    cBinFiberHist 6 3 = 4 ∧
    cBinFiberHist 6 4 = 9 ∧
    cBinFiberHist 6 5 = 0 ∧
    cBinFiberHist 6 2 * 2 + cBinFiberHist 6 3 * 3 + cBinFiberHist 6 4 * 4 = 64

/-- At `m = 6`, the stable-language carrier `X_6` and its histogram are fixed numerical
invariants. -/
def terminalCutProjectWindow6Invariant : Prop :=
  Fintype.card (X 6) = 21 ∧
    Fintype.card (X 6) = Nat.fib 8 ∧
    cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4 = Fintype.card (X 6)

/-- Paper-facing wrapper for the cut-and-project to fold-hist interface: the audited window-6
histogram factors through the finite stable-language object `X_6`, and the resulting `m = 6`
histogram is pinned down by implementation-independent constants.
    prop:terminal-cut-project-to-fold-hist -/
theorem paper_terminal_cut_project_to_fold_hist :
    terminalCutProjectFoldHistogramFactors ∧ terminalCutProjectWindow6Invariant := by
  refine ⟨?_, ?_⟩
  · refine ⟨cBinFiberHist_6_0, cBinFiberHist_6_1, cBinFiberHist_6_2, cBinFiberHist_6_3,
      cBinFiberHist_6_4, cBinFiberHist_6_5, ?_⟩
    rw [cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]
  · refine ⟨X.card_X_six, ?_, ?_⟩
    · rw [X.card_X_six]
      native_decide
    · rw [binFold6_distinct_multiplicities, X.card_X_six]

end Omega.GU
