import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6OffsetsReturnTimes
import Omega.GU.TerminalResetEventsSturmian
import Omega.GU.ZeckendorfCountClosure

namespace Omega.GU

private def terminalWindow6ResetWitness : TerminalResetEventsSturmianData where
  smallGap := 34
  largeGap := 55
  discrepancy := 1
  smallGap_eq := by native_decide
  largeGap_eq := by native_decide
  discrepancy_le_one := by native_decide

/-- Paper-facing wrapper: at window `6` the triple `21, 34, 55` is seen simultaneously as the
tail-offset package, the Sturmian reset-gap spectrum with recurrence `55 = 34 + 21`, and the
Zeckendorf/GUT top-term alignment `|X_6|, |X_7|, |X_8| = F_8, F_9, F_10`.
    thm:terminal-window6-unification-triple-dynamic -/
theorem paper_terminal_window6_unification_triple_dynamic :
    terminalFoldbin6TailOffsets = {21, 34, 55} ∧
      ({(34 : ℕ), 55} : Finset ℕ) = {Nat.fib 9, Nat.fib 10} ∧
      55 = 34 + 21 ∧
      21 = Fintype.card (Omega.X 6) ∧
      34 = Fintype.card (Omega.X 7) ∧
      55 = Fintype.card (Omega.X 8) ∧
      24 = 21 + Nat.fib 4 ∧
      45 = 34 + Nat.fib 6 + Nat.fib 4 ∧
      78 = 55 + 21 + Nat.fib 3 := by
  rcases paper_terminal_foldbin6_offsets_return_times with
    ⟨hOffsets, _, _, _, _, _, _⟩
  rcases fold6_tail_offsets with ⟨h8, h9, h10⟩
  rcases paper_terminal_reset_events_sturmian terminalWindow6ResetWitness with
    ⟨hTwoGap, hWord, _⟩
  rcases hWord with ⟨_, _, _, hGapRec⟩
  rcases fold6_tail_offsets_are_card_X with ⟨hX6, hX7, hX8⟩
  rcases gut_top_fibonacci_terms with ⟨hSu5, hSo10, hE6⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [terminalFoldbin6TailOffsets, h8, h9, h10] using hOffsets
  · simpa [terminalWindow6ResetWitness, TerminalResetEventsSturmianData.twoGapLaw] using hTwoGap
  · simpa [terminalWindow6ResetWitness, h8] using hGapRec
  · simpa [h8] using hX6
  · simpa [h9] using hX7
  · simpa [h10] using hX8
  · simpa [h8] using hSu5
  · simpa [h9] using hSo10
  · simpa [h8, h10] using hE6

end Omega.GU
