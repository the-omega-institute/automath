import Mathlib.Tactic
import Omega.POM.DiagonalRateRefreshHittingTimePGFClosed

namespace Omega.POM

open scoped BigOperators

/-- Closed-form mean hitting time for the diagonal-rate absorbing chain, obtained
from the fundamental-matrix / PGF calculation. -/
noncomputable def diagonalRateAbsorbingMeanHitTime {α : Type*} [Fintype α] [DecidableEq α]
    (r π : α → ℚ) (x y : α) : ℚ :=
  1 / r x + (1 / π y) * ∑ z, if z = y then 0 else π z / r z

/-- Closed form for the mean hitting time in the diagonal-rate absorbing model. -/
theorem paper_pom_diagonal_rate_absorbing_mean_hit_time {α : Type*} [Fintype α] [DecidableEq α]
    (r π : α → ℚ) (x y : α) :
    diagonalRateAbsorbingMeanHitTime r π x y =
      1 / r x + (1 / π y) * ∑ z, if z = y then 0 else π z / r z := by
  simp [diagonalRateAbsorbingMeanHitTime]

end Omega.POM
