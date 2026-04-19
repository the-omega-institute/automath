import Omega.GU.TerminalFoldbin6InformationLossConstants
import Omega.TypedAddressBiaxialCompletion.Window6ExplicitFibers

namespace Omega.TypedAddressBiaxialCompletion

open Omega.GU

/-- Chapter-local fixed-baseline audit package for the certified window-`6` instance: the
histogram, carrier size, information-loss constant, and induced KL gap are all recorded in one
conjunction. -/
theorem paper_typed_address_biaxial_completion_window6_audit_fixed_baseline :
    Omega.cBinFiberHist 6 2 = 8 ∧
      Omega.cBinFiberHist 6 3 = 4 ∧
      Omega.cBinFiberHist 6 4 = 9 ∧
      Fintype.card (Omega.X 6) = 21 ∧
      Omega.GU.terminalFoldbin6InformationLoss =
        (11 : ℝ) / 8 + (3 : ℝ) / 16 * Real.logb 2 3 ∧
      Omega.GU.terminalFoldbin6KLGap =
        Real.logb 2 21 - ((37 : ℝ) / 8 - (3 : ℝ) / 16 * Real.logb 2 3) := by
  rcases paper_terminal_foldbin6_information_loss_constants with
    ⟨h2, h3, h4, hcard, _, hloss, _, hkl⟩
  exact ⟨h2, h3, h4, hcard, hloss, hkl⟩

end Omega.TypedAddressBiaxialCompletion
