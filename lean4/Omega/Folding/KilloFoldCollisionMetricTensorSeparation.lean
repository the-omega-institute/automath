import Mathlib.Tactic
import Omega.Folding.CollisionKernel

namespace Omega.Folding

/-- Paper label: `cor:killo-fold-collision-metric-tensor-separation`. -/
theorem paper_killo_fold_collision_metric_tensor_separation (t : ℤ) :
    charPolyA4t t = fun x => (-2 * x ^ 4 + 2) + (x ^ 5 - t * x ^ 3 - 2 * x) := by
  funext x
  unfold charPolyA4t
  ring

end Omega.Folding
