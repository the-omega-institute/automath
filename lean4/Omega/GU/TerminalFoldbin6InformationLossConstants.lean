import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.GU

/-- The window-`6` pushforward expectation `E[log₂ d]` attached to the certified multiplicity
histogram `(2:8, 3:4, 4:9)`. -/
noncomputable def terminalFoldbin6InformationLoss : ℝ :=
  ((8 : ℝ) * 2 * Real.logb 2 2 + (4 : ℝ) * 3 * Real.logb 2 3 +
      (9 : ℝ) * 4 * Real.logb 2 4) / 64

/-- The output Shannon entropy `H₂(W) = 6 - E[log₂ d]`. -/
noncomputable def terminalFoldbin6Entropy : ℝ :=
  6 - terminalFoldbin6InformationLoss

/-- The KL gap from the uniform law on `X₆`. -/
noncomputable def terminalFoldbin6KLGap : ℝ :=
  Real.logb 2 21 - terminalFoldbin6Entropy

private theorem logb_two_two : Real.logb 2 (2 : ℝ) = 1 := by
  exact Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num)

private theorem logb_two_four : Real.logb 2 (4 : ℝ) = 2 := by
  calc
    Real.logb 2 (4 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
    _ = (2 : ℕ) * Real.logb 2 (2 : ℝ) := by rw [Real.logb_pow]
    _ = 2 := by rw [logb_two_two]; norm_num

private theorem information_loss_closed_form :
    terminalFoldbin6InformationLoss = (11 : ℝ) / 8 + (3 : ℝ) / 16 * Real.logb 2 3 := by
  unfold terminalFoldbin6InformationLoss
  rw [logb_two_two, logb_two_four]
  ring

/-- Paper-facing window-`6` information-loss constants extracted from the certified histogram
`(2:8, 3:4, 4:9)`: the pushforward expectation `E[log₂ d]`, the entropy identity
`H₂(W)=6-E[log₂ d]`, and the induced uniform KL gap.
    thm:terminal-foldbin6-information-loss-constants -/
theorem paper_terminal_foldbin6_information_loss_constants :
    cBinFiberHist 6 2 = 8 ∧
    cBinFiberHist 6 3 = 4 ∧
    cBinFiberHist 6 4 = 9 ∧
    Fintype.card (X 6) = 21 ∧
    terminalFoldbin6Entropy = 6 - terminalFoldbin6InformationLoss ∧
    terminalFoldbin6InformationLoss = (11 : ℝ) / 8 + (3 : ℝ) / 16 * Real.logb 2 3 ∧
    terminalFoldbin6Entropy = (37 : ℝ) / 8 - (3 : ℝ) / 16 * Real.logb 2 3 ∧
    terminalFoldbin6KLGap =
      Real.logb 2 21 - ((37 : ℝ) / 8 - (3 : ℝ) / 16 * Real.logb 2 3) := by
  refine ⟨cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4, ?_, rfl,
    information_loss_closed_form, ?_, ?_⟩
  · rw [X.card_eq_fib]
    native_decide
  · unfold terminalFoldbin6Entropy
    rw [information_loss_closed_form]
    ring
  · unfold terminalFoldbin6KLGap terminalFoldbin6Entropy
    rw [information_loss_closed_form]
    ring

end Omega.GU
