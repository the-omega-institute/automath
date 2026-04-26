import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.CollisionKernel
import Omega.Folding.ShiftDynamics

namespace Omega.Folding

/-- Paper label: `thm:killo-fold-collision-bowen-franks-q5-break`. -/
theorem paper_killo_fold_collision_bowen_franks_q5_break :
    Int.natAbs Omega.bowenFranksMatrix5.det = 32 ∧
      Int.natAbs Omega.bowenFranksMatrix5.det - Nat.fib 8 = Omega.lucasNum 5 ∧
      Omega.collisionKernel5.trace = -2 := by
  refine ⟨?_, ?_, Omega.collisionKernel5_trace⟩
  · rw [Omega.bowenFranksMatrix5_det]
    norm_num
  · rw [Omega.bowenFranksMatrix5_det]
    norm_num [Nat.fib, Omega.lucasNum]

end Omega.Folding
