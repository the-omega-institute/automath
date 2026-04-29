import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-gauge-constant-one-step-acceleration-2pi`. -/
theorem paper_xi_foldbin_gauge_constant_one_step_acceleration_2pi
    (logC logCacc leading cubic tail : ℕ → ℝ)
    (hacc : ∀ m, logCacc m = logC m - leading m)
    (hexp : ∀ m, logC m - Real.log (2 * Real.pi) = leading m + cubic m + tail m) :
    ∀ m, logCacc m - Real.log (2 * Real.pi) = cubic m + tail m := by
  intro m
  calc
    logCacc m - Real.log (2 * Real.pi) =
        (logC m - leading m) - Real.log (2 * Real.pi) := by
          rw [hacc m]
    _ = (logC m - Real.log (2 * Real.pi)) - leading m := by ring
    _ = (leading m + cubic m + tail m) - leading m := by rw [hexp m]
    _ = cubic m + tail m := by ring

end Omega.Zeta
