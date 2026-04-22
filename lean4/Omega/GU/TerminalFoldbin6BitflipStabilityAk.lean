import Omega.GU.TerminalFoldbin6BitflipStabilityPolynomial

namespace Omega.GU

abbrev TerminalFoldbin6BitflipStabilityAkData := PUnit

def TerminalFoldbin6BitflipStabilityAkStatement (_ : TerminalFoldbin6BitflipStabilityAkData) :
    Prop :=
  terminalFoldbin6StabilityCoeff 0 = 1 ∧
    terminalFoldbin6StabilityCoeff 1 = 0 ∧
    terminalFoldbin6StabilityCoeff 2 = 1 / 30 ∧
    terminalFoldbin6StabilityCoeff 3 = 1 / 40 ∧
    terminalFoldbin6StabilityCoeff 4 = 7 / 120 ∧
    terminalFoldbin6StabilityCoeff 5 = 1 / 16 ∧
    terminalFoldbin6StabilityCoeff 6 = 1 / 16

/-- Paper label: `cor:terminal-foldbin6-bitflip-stability-Ak`. -/
theorem paper_terminal_foldbin6_bitflip_stability_ak
    (D : TerminalFoldbin6BitflipStabilityAkData) : TerminalFoldbin6BitflipStabilityAkStatement D := by
  simpa [TerminalFoldbin6BitflipStabilityAkStatement] using paper_terminal_foldbin6_bitflip_stability_Ak

end Omega.GU
