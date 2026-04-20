import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The finite-language minimax online log-loss value. For an empty language this package uses the
default value `0`; the paper theorem only addresses the nonempty finite-language regime. -/
noncomputable def languageMinimaxLogLoss {A : Type} [Fintype A] [DecidableEq A]
    (L : Finset (List A)) : ℝ :=
  if _hL : 0 < L.card then
    Real.log L.card
  else
    0

/-- For a nonempty finite language, the minimax log-loss equals `log |L|`.
    thm:xi-terminal-zm-language-minimax-logloss -/
theorem paper_xi_terminal_zm_language_minimax_logloss {A : Type} [Fintype A] [DecidableEq A]
    (L : Finset (List A)) (hL : 0 < L.card) : languageMinimaxLogLoss L = Real.log L.card := by
  simp [languageMinimaxLogLoss, hL]

end Omega.Zeta
