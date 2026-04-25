import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.GroupUnification

/-- The audited `m = 7` uplift-delta row. -/
def sm_uplift_residual_mediator_m7_row : Finset ℕ := {0, 55, 89}

/-- The second difference extracted from the nonzero entries of the audited `m = 7` row. -/
def sm_uplift_residual_mediator_m7_second_difference : ℕ := 89 - 55

/-- Paper label: `prop:sm-uplift-residual-mediator-m7`. The audited `m = 7` uplift row carries the
residual channel `34`, and the same value is the concrete `m = 7` instance of the boundary
second-difference residual law. -/
theorem paper_sm_uplift_residual_mediator_m7 :
    sm_uplift_residual_mediator_m7_row = ({0, 55, 89} : Finset ℕ) ∧
      sm_uplift_residual_mediator_m7_second_difference = 34 ∧
      Nat.fib 11 - Nat.fib 10 = sm_uplift_residual_mediator_m7_second_difference := by
  have hsecond : sm_uplift_residual_mediator_m7_second_difference = 34 := by
    norm_num [sm_uplift_residual_mediator_m7_second_difference]
  have hlaw : Nat.fib 11 - Nat.fib 10 = Nat.fib 9 := Omega.bdry_uplift_second_diff_m7
  have hfib9 : Nat.fib 9 = 34 := by
    native_decide
  refine ⟨rfl, hsecond, ?_⟩
  rw [hsecond]
  exact hlaw.trans hfib9

end Omega.GroupUnification
