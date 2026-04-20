import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6FiberHammingMinDistanceHistogram
import Omega.GU.TerminalFoldbin6TwoPointFiberDirectionSpectrum

namespace Omega.GU

/-- Removing the three audited two-point direction classes from the global minimum-Hamming
histogram leaves no heavy fiber at distance `5`. -/
theorem paper_window6_heavy_fiber_no_max_distance :
    cBinFiberMinHammingHist 6 2 - (terminalFoldbin6FiberValuesByDirection 34).length = 9 ∧
      cBinFiberMinHammingHist 6 3 - (terminalFoldbin6FiberValuesByDirection 38).length = 4 ∧
      cBinFiberMinHammingHist 6 5 - (terminalFoldbin6FiberValuesByDirection 62).length = 0 := by
  rcases paper_terminal_foldbin6_fiber_hamming_min_distance_histogram with ⟨h2, h3, h5⟩
  rcases paper_terminal_foldbin6_two_point_fiber_direction_spectrum with
    ⟨_, _, h34, h38, h62, _⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h2, h34]
    norm_num
  · rw [h3, h38]
    norm_num
  · rw [h5, h62]
    norm_num

end Omega.GU
