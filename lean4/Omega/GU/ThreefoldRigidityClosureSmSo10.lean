import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.GU.NapLocalUpliftForcesSo10
import Omega.GU.ThreefoldRigidity

namespace Omega.GU

/-- Publication-facing closure package combining window-6 threefold rigidity with the local-uplift
to `so(10)` consequence.
    cor:window6-threefold-rigidity-closure-sm-so10 -/
theorem paper_window6_threefold_rigidity_closure_sm_so10 :
    (Nat.fib 9 ≤ 15 * 3 ∧ 15 * 3 < Nat.fib 10) ∧
      (15 * 1 < Nat.fib 9 ∧ 15 * 2 < Nat.fib 9) ∧
      Nat.fib 10 ≤ 15 * 4 ∧
      terminalFoldbin6BoundaryOffsets = {Nat.fib 9} ∧
      45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 := by
  rcases Omega.GU.ThreefoldRigidity.paper_window6_threefold_rigidity with
    ⟨hRange, hSmall, hLarge, _hFib9, _hFib4⟩
  rcases paper_gut_nap_local_uplift_forces_so10 with ⟨hBoundary, hSo10⟩
  exact ⟨hRange, hSmall, hLarge, hBoundary, hSo10⟩

end Omega.GU
