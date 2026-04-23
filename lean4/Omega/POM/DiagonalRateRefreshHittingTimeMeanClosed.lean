import Omega.POM.DiagonalRateAbsorbingMeanHitTime

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `cor:pom-diagonal-rate-refresh-hitting-time-mean-closed`.
The closed-form PGF packages the first holding time and the geometric number of failed refresh
rounds, so the expectation collapses to the displayed rational sum. -/
theorem paper_pom_diagonal_rate_refresh_hitting_time_mean_closed
    {α : Type*} [Fintype α] [DecidableEq α] (r π : α → ℚ) (x y : α) :
    diagonalRateAbsorbingMeanHitTime r π x y =
      1 / r x + (1 / π y) * ∑ z, if z = y then 0 else π z / r z := by
  simpa using paper_pom_diagonal_rate_absorbing_mean_hit_time (r := r) (π := π) (x := x) (y := y)

end Omega.POM
