import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.CollisionKernel

namespace Omega.Folding

/-- Paper label: `thm:killo-fold-collision-bowen-franks-fibonacci-bisection`. -/
theorem paper_killo_fold_collision_bowen_franks_fibonacci_bisection :
    Int.natAbs Omega.bowenFranksMatrix2.det = Nat.fib 2 ∧
      Int.natAbs Omega.bowenFranksMatrix3.det = Nat.fib 4 ∧
      Int.natAbs Omega.bowenFranksMatrix4.det = Nat.fib 6 ∧
      Nat.fib 6 = 3 * Nat.fib 4 - Nat.fib 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Omega.bowenFranksMatrix2_det]
    norm_num [Nat.fib]
  · rw [Omega.bowenFranksMatrix3_det]
    norm_num [Nat.fib]
  · rw [Omega.bowenFranksMatrix4_det]
    norm_num [Nat.fib]
  · norm_num [Nat.fib]

end Omega.Folding
