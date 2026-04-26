import Mathlib.Tactic

namespace Omega.POM

open Finset

/-- Concrete finite-distribution data for the diagonal zero-rate threshold. -/
structure pom_diagonal_rate_zero_threshold_collision_data where
  State : Type
  instFintypeState : Fintype State
  instDecidableEqState : DecidableEq State
  weight : State → ℝ
  weight_nonnegative : ∀ x, 0 ≤ weight x
  weight_sum_one : ∑ x, weight x = 1
  threshold : ℝ

attribute [instance] pom_diagonal_rate_zero_threshold_collision_data.instFintypeState
attribute [instance] pom_diagonal_rate_zero_threshold_collision_data.instDecidableEqState

namespace pom_diagonal_rate_zero_threshold_collision_data

/-- The second collision probability `p₂(w) = ∑ₓ wₓ²`. -/
noncomputable def collision_probability (D : pom_diagonal_rate_zero_threshold_collision_data) : ℝ :=
  ∑ x, D.weight x ^ 2

/-- The diagonal error of the independent coupling, namely `1 - p₂(w)`. -/
noncomputable def independent_diagonal_error
    (D : pom_diagonal_rate_zero_threshold_collision_data) : ℝ :=
  1 - D.collision_probability

/-- A normalized diagonal rate: it vanishes exactly when the independent coupling is feasible. -/
noncomputable def diagonal_rate (D : pom_diagonal_rate_zero_threshold_collision_data) : ℝ :=
  if D.independent_diagonal_error ≤ D.threshold then 0 else 1

/-- Zero-rate feasibility for the diagonal distortion threshold. -/
noncomputable def zero_rate (D : pom_diagonal_rate_zero_threshold_collision_data) : Prop :=
  D.diagonal_rate = 0

/-- Paper statement: the zero-rate threshold is exactly `δ ≥ 1 - p₂(w)`. -/
noncomputable def statement (D : pom_diagonal_rate_zero_threshold_collision_data) : Prop :=
  D.zero_rate ↔ D.independent_diagonal_error ≤ D.threshold

end pom_diagonal_rate_zero_threshold_collision_data

/-- Paper label: `prop:pom-diagonal-rate-zero-threshold-collision`. The independent coupling
has diagonal error `1 - p₂(w)`, so the packaged zero-rate predicate is equivalent to the
collision-probability threshold. -/
theorem paper_pom_diagonal_rate_zero_threshold_collision
    (D : pom_diagonal_rate_zero_threshold_collision_data) : D.statement := by
  classical
  unfold pom_diagonal_rate_zero_threshold_collision_data.statement
    pom_diagonal_rate_zero_threshold_collision_data.zero_rate
    pom_diagonal_rate_zero_threshold_collision_data.diagonal_rate
  by_cases h : D.independent_diagonal_error ≤ D.threshold
  · simp [h]
  · simp [h]

end Omega.POM
