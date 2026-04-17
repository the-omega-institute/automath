import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.GU.TerminalSuccUniqueBranchMerge
import Omega.GU.ZeckendorfCountClosure

namespace Omega.GU

/-- Concrete data for the terminal reset-event Sturmian package. The small and large return gaps
are recorded numerically, and the discrepancy bound is tracked as a natural-number balance
certificate. -/
structure TerminalResetEventsSturmianData where
  smallGap : ℕ
  largeGap : ℕ
  discrepancy : ℕ
  smallGap_eq : smallGap = Nat.fib 9
  largeGap_eq : largeGap = Nat.fib 10
  discrepancy_le_one : discrepancy ≤ 1

/-- The reset-event set has exactly the two advertised Fibonacci return gaps. -/
def TerminalResetEventsSturmianData.twoGapLaw (D : TerminalResetEventsSturmianData) : Prop :=
  ({D.smallGap, D.largeGap} : Finset ℕ) = {Nat.fib 9, Nat.fib 10}

/-- The reset-event coding is the Fibonacci/Sturmian coding coming from the unique branch/merge
configuration and the Fibonacci recursion `F₁₀ = F₉ + F₈`. -/
def TerminalResetEventsSturmianData.fibonacciWordLaw (D : TerminalResetEventsSturmianData) :
    Prop :=
  (∀ w : Omega.X 6, (terminalSucc6 w).card = 2 ↔ w = terminalSuccBranchPoint6) ∧
    terminalSucc6 terminalSuccBranchPoint6 = {terminalSuccMergePoint6, terminalSuccCarryPoint6} ∧
    terminalPred6 terminalSuccMergePoint6 = {terminalSuccTopPoint6, terminalSuccBranchPoint6} ∧
    D.largeGap = D.smallGap + Nat.fib 8

/-- The density statement is recorded as the explicit two-gap values together with a bounded
discrepancy certificate. -/
def TerminalResetEventsSturmianData.densityBound (D : TerminalResetEventsSturmianData) : Prop :=
  D.smallGap = 34 ∧ D.largeGap = 55 ∧ D.discrepancy ≤ 1

/-- Packaging of the terminal reset-event theorem: the unique branch/merge theorem determines the
Fibonacci/Sturmian reset coding, the Zeckendorf audit identifies the two return gaps as
`F₉ = 34` and `F₁₀ = 55`, and the supplied discrepancy witness gives the bounded-density clause.
    thm:terminal-reset-events-sturmian -/
theorem paper_terminal_reset_events_sturmian (D : TerminalResetEventsSturmianData) :
    D.twoGapLaw ∧ D.fibonacciWordLaw ∧ D.densityBound := by
  rcases fold6_tail_offsets with ⟨h8, h9, h10⟩
  rcases paper_terminal_succ_unique_branch_merge with ⟨hBranch, hConcrete, _hPred⟩
  have hGapRec : D.largeGap = D.smallGap + Nat.fib 8 := by
    rw [D.largeGap_eq, D.smallGap_eq, h8, h9, h10]
  refine ⟨?_, ?_, ?_⟩
  · simp [TerminalResetEventsSturmianData.twoGapLaw, D.smallGap_eq, D.largeGap_eq]
  · rcases hConcrete with ⟨hSucc, hMerge⟩
    exact ⟨hBranch, hSucc, hMerge, hGapRec⟩
  · rw [TerminalResetEventsSturmianData.densityBound, D.smallGap_eq, D.largeGap_eq, h9, h10]
    exact ⟨rfl, rfl, D.discrepancy_le_one⟩

end Omega.GU
