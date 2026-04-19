import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.GU

/-- Paper-facing wrapper for the window-6 fiber minimum-Hamming histogram counts.
    cor:terminal-foldbin6-fiber-hamming-min-distance-histogram -/
theorem paper_terminal_foldbin6_fiber_hamming_min_distance_histogram :
    cBinFiberMinHammingHist 6 2 = 13 ∧
      cBinFiberMinHammingHist 6 3 = 6 ∧
      cBinFiberMinHammingHist 6 5 = 2 := by
  exact ⟨binFiber6_minHamming_hist_2, binFiber6_minHamming_hist_3, binFiber6_minHamming_hist_5⟩

end Omega.GU
