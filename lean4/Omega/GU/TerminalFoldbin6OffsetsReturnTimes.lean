import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6BoundaryPureF9Alias
import Omega.GU.TerminalFoldbin6ThreeOffsetRigidity

namespace Omega.GU

/-- Paper-facing wrapper: the three nontrivial window-6 offsets are exactly the consecutive
golden return-time scales `F₈, F₉, F₁₀`, while the boundary sector selects the middle alias `F₉`.
    cor:terminal-foldbin6-offsets-return-times -/
theorem paper_terminal_foldbin6_offsets_return_times :
    terminalFoldbin6TailOffsets = {Nat.fib 8, Nat.fib 9, Nat.fib 10} ∧
      terminalFoldbin6BoundaryOffsets = {Nat.fib 9} ∧
      terminalFoldbin6TailOffset ⟨true, false, false⟩ = Nat.fib 8 ∧
      terminalFoldbin6TailOffset ⟨false, true, false⟩ = Nat.fib 9 ∧
      terminalFoldbin6TailOffset ⟨false, false, true⟩ = Nat.fib 10 ∧
      cBinFiberHist 6 1 = 0 ∧
      cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4 = 21 := by
  rcases paper_terminal_foldbin6_boundary_pure_f9_alias 0 with ⟨hOffsets, hBoundary, _⟩
  rcases paper_terminal_foldbin6_three_offset_rigidity with
    ⟨h8, h9, h10, hHist1, hHist234⟩
  exact ⟨hOffsets, hBoundary, h8, h9, h10, hHist1, hHist234⟩

end Omega.GU
