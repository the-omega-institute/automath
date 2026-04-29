import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-leyang-cubic-rational-observable-primitivity`. -/
theorem paper_xi_terminal_zm_leyang_cubic_rational_observable_primitivity {L α : Type*}
    [PartialOrder L] (bot top : L) (span : α → L)
    (hnoIntermediate : ∀ M, bot < M → M ≤ top → M = top) (z : α)
    (hzNonrat : bot < span z) (hzUpper : span z ≤ top) :
    span z = top := by
  exact hnoIntermediate (span z) hzNonrat hzUpper

end Omega.Zeta
