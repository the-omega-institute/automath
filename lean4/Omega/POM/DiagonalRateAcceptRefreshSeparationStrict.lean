import Mathlib.Tactic
import Omega.POM.DiagonalRateAcceptRefreshSeparationExact

namespace Omega.POM

/-- Strengthening of the exact accept-refresh separation package by ruling out equality away from
the designated halting state. -/
structure DiagonalRateAcceptRefreshSeparationStrictData
    extends DiagonalRateAcceptRefreshSeparationExactData where
  ratio_eq_at_halting_witness : ∀ {y m}, ratio h m = ratio y m → y = h

/-- Paper label: `cor:pom-diagonal-rate-accept-refresh-separation-strict`.
Away from the unique halting state, the exact minimizer from the accept-refresh package is strict.
-/
theorem paper_pom_diagonal_rate_accept_refresh_separation_strict
    (D : DiagonalRateAcceptRefreshSeparationStrictData) :
    ∀ y m, y ≠ D.h -> D.ratio D.h m < D.ratio y m := by
  intro y m hy
  have hle : D.ratio D.h m ≤ D.ratio y m := D.haltingStateWorst_witness y m
  have hne : D.ratio D.h m ≠ D.ratio y m := by
    intro heq
    exact hy (D.ratio_eq_at_halting_witness heq)
  exact lt_of_le_of_ne hle hne

end Omega.POM
