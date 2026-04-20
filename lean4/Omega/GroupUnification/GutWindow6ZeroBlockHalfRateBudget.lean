import Mathlib.Tactic
import Omega.GroupUnification.TerminalWindow6OneEightTwelveSplit

namespace Omega.GroupUnification

/-- Concrete data wrapper for the window-6 zero-block half-rate audit. All quantities are computed
from the explicit `1 ⊕ 8 ⊕ 12` terminal split, so the structure itself carries no abstract proof
payload. -/
structure GutWindow6ZeroBlockHalfRateBudgetData where

namespace GutWindow6ZeroBlockHalfRateBudgetData

/-- The zero-block sector used for the half-rate audit is the heavy `12`-element window-6 block. -/
def zeroBlockSet (_D : GutWindow6ZeroBlockHalfRateBudgetData) : Finset Window6StableWord :=
  window6HeavySector

/-- The cardinality of the audited zero block. -/
def zeroBlockCard (D : GutWindow6ZeroBlockHalfRateBudgetData) : ℕ :=
  D.zeroBlockSet.card

/-- The audited zero block covers at least half of the Fibonacci state count `F₈ = 21`. -/
def halfRateLowerBound (D : GutWindow6ZeroBlockHalfRateBudgetData) : Prop :=
  Nat.fib 8 / 2 ≤ D.zeroBlockCard

/-- Equivalently, the zero block occupies at least a half-scale share of the full window-6 state
space. -/
def halfScaleShareFormula (D : GutWindow6ZeroBlockHalfRateBudgetData) : Prop :=
  Nat.fib 8 ≤ 2 * D.zeroBlockCard

/-- Four binary audit bits suffice to inject the zero block into a Boolean register ledger. -/
def injectionBitBudget (D : GutWindow6ZeroBlockHalfRateBudgetData) : Prop :=
  D.zeroBlockCard ≤ 2 ^ 4

end GutWindow6ZeroBlockHalfRateBudgetData

open GutWindow6ZeroBlockHalfRateBudgetData

private lemma gutWindow6_zeroBlockCard :
    ∀ D : GutWindow6ZeroBlockHalfRateBudgetData, D.zeroBlockCard = 12 := by
  intro D
  simpa [GutWindow6ZeroBlockHalfRateBudgetData.zeroBlockCard,
    GutWindow6ZeroBlockHalfRateBudgetData.zeroBlockSet] using
    (paper_terminal_window6_1_8_12_split).2.2.1

/-- Paper label: `thm:gut-window6-zero-block-half-rate-budget`. -/
theorem paper_gut_window6_zero_block_half_rate_budget (D : GutWindow6ZeroBlockHalfRateBudgetData) :
    D.halfRateLowerBound ∧ D.halfScaleShareFormula ∧ D.injectionBitBudget := by
  have hcard : D.zeroBlockCard = 12 := gutWindow6_zeroBlockCard D
  refine ⟨?_, ?_, ?_⟩
  · rw [GutWindow6ZeroBlockHalfRateBudgetData.halfRateLowerBound, hcard]
    native_decide
  · rw [GutWindow6ZeroBlockHalfRateBudgetData.halfScaleShareFormula, hcard]
    native_decide
  · rw [GutWindow6ZeroBlockHalfRateBudgetData.injectionBitBudget, hcard]
    native_decide

end Omega.GroupUnification
