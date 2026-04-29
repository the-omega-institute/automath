import Mathlib.Tactic
import Omega.Zeta.SyncActionGap

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Finite-support wrapper for the Newton-support extreme slopes: witnesses for the minimum and
maximum density already live in the positive primitive support, and the lower endpoint is bounded
by the upper endpoint.
    prop:sync-newton-extreme-slopes -/
theorem paper_sync_newton_extreme_slopes
    (primitiveCycles : Finset PrimitiveCycle) (primitiveCount : PrimitiveCycle → ℕ)
    (density : PrimitiveCycle → ℚ) (alphaMin alphaMax : ℚ)
    (hmin : ∀ cycle ∈ positivePrimitiveSupport primitiveCycles primitiveCount, alphaMin ≤ density cycle)
    (hmin_witness :
      ∃ cycle ∈ positivePrimitiveSupport primitiveCycles primitiveCount, density cycle = alphaMin)
    (hmax : ∀ cycle ∈ positivePrimitiveSupport primitiveCycles primitiveCount, density cycle ≤ alphaMax)
    (hmax_witness :
      ∃ cycle ∈ positivePrimitiveSupport primitiveCycles primitiveCount, density cycle = alphaMax) :
    (∃ cycle ∈ positivePrimitiveSupport primitiveCycles primitiveCount, density cycle = alphaMin) ∧
      (∃ cycle ∈ positivePrimitiveSupport primitiveCycles primitiveCount, density cycle = alphaMax) ∧
      alphaMin ≤ alphaMax := by
  rcases hmin_witness with ⟨cycleMin, hcycleMin, hcycleMin_eq⟩
  rcases hmax_witness with ⟨cycleMax, hcycleMax, hcycleMax_eq⟩
  refine ⟨⟨cycleMin, hcycleMin, hcycleMin_eq⟩, ⟨cycleMax, hcycleMax, hcycleMax_eq⟩, ?_⟩
  have hLower : alphaMin ≤ density cycleMin := hmin cycleMin hcycleMin
  have hUpper : density cycleMin ≤ alphaMax := hmax cycleMin hcycleMin
  rw [hcycleMin_eq] at hUpper
  exact hUpper
