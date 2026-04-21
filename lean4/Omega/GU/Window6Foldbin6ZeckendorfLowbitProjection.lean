import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6BoundaryPureF9Alias
import Omega.GU.TerminalFoldbin6ThreeOffsetRigidity
import Omega.GU.TerminalFoldbin6OffsetsReturnTimes
import Omega.GU.TerminalOstrowskiZeckendorfBinfold

namespace Omega.GU

/-- Paper label: `lem:window6-foldbin6-zeckendorf-lowbit-projection`. -/
theorem paper_window6_foldbin6_zeckendorf_lowbit_projection (n : Nat) (hn : n < 64) :
    (∀ i : Fin 6, (Omega.cBinFold 6 n).1 i = true ↔ i.1 + 2 ∈ Nat.zeckendorf n) ∧
      Omega.GU.terminalFoldbin6TailOffsets = ({Nat.fib 8, Nat.fib 9, Nat.fib 10} : Finset Nat) := by
  have _ := hn
  have hBits := (paper_terminal_ostrowski_zeckendorf_binfold 6 n).2.2.1
  have hOffsets' : terminalFoldbin6TailOffsets = ({Nat.fib 8, Nat.fib 9, Nat.fib 10} : Finset Nat) := by
    exact (paper_terminal_foldbin6_boundary_pure_f9_alias 0).1
  have hOffsets := paper_terminal_foldbin6_offsets_return_times.1
  exact ⟨hBits, hOffsets⟩

end Omega.GU
