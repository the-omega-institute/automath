import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `thm:dual-boundary-normal-form`.
Simultaneously shifting both boundary depths by the same logarithmic time leaves the transverse
invariant `I = Y_r - Y_t` unchanged. -/
theorem paper_dual_boundary_normal_form (Y_r Y_t logm : ℝ) :
    let I := Y_r - Y_t
    let Y_r' := Y_r + logm
    let Y_t' := Y_t + logm
    Y_r' - Y_t' = I := by
  dsimp
  ring

end Omega.UnitCirclePhaseArithmetic
