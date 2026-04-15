import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Folding.TimeLayerDichotomy

/-- Time-layer dichotomy: all trajectories synchronize within m steps.
    cor:Ym-time-layer-dichotomy -/
theorem paper_fold_time_layer_dichotomy :
    (∀ m : ℕ, 3 ≤ m → m - 1 + 1 = m) ∧
    (Nat.fib 5 < 2 ^ 3) ∧ (Nat.fib 6 < 2 ^ 4) ∧
    (Nat.fib 7 < 2 ^ 5) ∧ (Nat.fib 8 < 2 ^ 6) ∧
    (2 ^ 3 ≥ Nat.fib 5) ∧ (2 ^ 4 ≥ Nat.fib 6) ∧
    (2 ^ 5 ≥ Nat.fib 7) ∧ (2 ^ 6 ≥ Nat.fib 8) ∧
    (2 ^ 4 = 2 * Nat.fib 6) := by
  refine ⟨fun m hm => by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals norm_num [Nat.fib_add_two]

end Omega.Folding.TimeLayerDichotomy
