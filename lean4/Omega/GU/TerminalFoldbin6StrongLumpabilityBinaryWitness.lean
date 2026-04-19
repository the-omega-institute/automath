import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic
import Omega.Folding.ZeckendorfSignature
import Omega.GU.TerminalFoldbin6StrongLumpabilityFails

namespace Omega.GU

/-- The first Zeckendorf tail bit discarded by the window-6 fold: the `F₈` digit. -/
def terminalFoldbin6BinaryWitness (n : Nat) : Nat :=
  if 8 ∈ Nat.zeckendorf n then 1 else 0

/-- Paper-facing binary witness statement extracted from the window-6 strong-lumpability
counterexample. -/
def TerminalFoldbin6StrongLumpabilityBinaryWitnessStatement : Prop :=
  cBinFold 6 0 = cBinFold 6 21 ∧
  21 = Nat.fib 8 ∧
  Nat.zeckendorf 0 = [] ∧
  Nat.zeckendorf 21 = [8] ∧
  terminalFoldbin6BinaryWitness 0 = 0 ∧
  terminalFoldbin6BinaryWitness 21 = 1 ∧
  terminalFoldbin6BinaryWitness 0 ≠ terminalFoldbin6BinaryWitness 21 ∧
  ∃ y : X 6,
    ((Finset.range 6).filter (fun k => cBinFold 6 (0 ^^^ (2 ^ k)) = y)).card ≠
      ((Finset.range 6).filter (fun k => cBinFold 6 (21 ^^^ (2 ^ k)) = y)).card

/-- The strong-lumpability counterexample at window 6 is separated by the Zeckendorf `F₈` tail
bit: `0` has witness `0`, while `21 = F₈` has witness `1`. -/
theorem paper_terminal_foldbin6_strong_lumpability_binary_witness :
    TerminalFoldbin6StrongLumpabilityBinaryWitnessStatement := by
  rcases paper_terminal_foldbin6_strong_lumpability_fails with ⟨hfold, hy⟩
  have h0 : terminalFoldbin6BinaryWitness 0 = 0 := by native_decide
  have h21 : terminalFoldbin6BinaryWitness 21 = 1 := by native_decide
  refine ⟨hfold, Omega.ZeckSig.fib_8_val.symm, ?_, ?_, h0, h21, ?_, hy⟩
  · native_decide
  · native_decide
  · simpa [h0, h21]

end Omega.GU
