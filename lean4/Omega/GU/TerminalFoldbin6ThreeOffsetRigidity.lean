import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.GU.TerminalFoldbin6TailCubeSection

namespace Omega.GU

/-- Paper-facing rigidity package for the three nontrivial window-6 tail offsets and the
    resulting fiber histogram support.
    cor:terminal-foldbin6-three-offset-rigidity -/
theorem paper_terminal_foldbin6_three_offset_rigidity :
    terminalFoldbin6TailOffset ⟨true, false, false⟩ = Nat.fib 8 ∧
      terminalFoldbin6TailOffset ⟨false, true, false⟩ = Nat.fib 9 ∧
      terminalFoldbin6TailOffset ⟨false, false, true⟩ = Nat.fib 10 ∧
      cBinFiberHist 6 1 = 0 ∧
      cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4 = 21 := by
  rcases paper_terminal_foldbin6_tail_cube_section 0 0 with
    ⟨_, h8, h9, h10, _, _⟩
  refine ⟨h8, h9, h10, cBinFiberHist_6_1, ?_⟩
  rw [cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]

end Omega.GU
