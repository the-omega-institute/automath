import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6MinReturnDelay

namespace Omega.GU

/-- A one-bit scan step cannot stay inside a single `cBinFold` fiber at window `6`.
    cor:terminal-foldbin6-onebit-error-detecting -/
theorem paper_terminal_foldbin6_onebit_error_detecting {u v : Fin 64}
    (h : terminalFoldbin6CubeStep u v) : cBinFold 6 u.1 ≠ cBinFold 6 v.1 := by
  have hChain : List.IsChain terminalFoldbin6CubeStep [u, v] := by
    simpa using h
  have hNoDwell := paper_terminal_foldbin6_no_dwell hChain
  simpa [terminalFoldbin6NoDwell] using hNoDwell

end Omega.GU
