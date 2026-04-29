import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.GroupUnification

/-- Paper label: `thm:bdry-uplift-second-difference-residual-law`. -/
theorem paper_bdry_uplift_second_difference_residual_law :
    Nat.fib 11 - Nat.fib 10 = Nat.fib 9 ∧ Nat.fib 12 - Nat.fib 11 = Nat.fib 10 ∧
      Nat.fib 9 = 34 ∧ Nat.fib 10 = 55 := by
  exact ⟨Omega.bdry_uplift_second_diff_m7, Omega.bdry_uplift_second_diff_m8, by native_decide,
    by native_decide⟩

end Omega.GroupUnification
