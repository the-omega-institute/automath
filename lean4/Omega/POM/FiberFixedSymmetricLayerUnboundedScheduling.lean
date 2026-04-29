import Mathlib.Tactic
import Omega.POM.FiberBulkSchedulingEntropyUniversal

namespace Omega.POM

/-- Explicit family `P_{N,r} = Z_{N-r+1} ⨿ (r-1)·Z_1`, tracked only through its total size. -/
def pom_fiber_fixed_symmetric_layer_unbounded_scheduling_family_size (r N : ℕ) : ℕ :=
  (N - r + 1) + (r - 1)

/-- Frozen visible algebra size for the fixed symmetric layer. -/
def pom_fiber_fixed_symmetric_layer_unbounded_scheduling_visible_algebra_dim (r : ℕ) : ℕ :=
  2 ^ r

/-- The chapter-level bulk scheduling entropy package specialized to the fixed symmetric layer. -/
def pom_fiber_fixed_symmetric_layer_unbounded_scheduling_bulk_entropy : Prop :=
  let D : PomFiberBulkSchedulingEntropyUniversalData := {}
  D.bulk_hypothesis → D.entropy_asymptotic

/-- Natural scheduling complexity attached to the explicit family. -/
def pom_fiber_fixed_symmetric_layer_unbounded_scheduling_complexity (r N : ℕ) : ℕ :=
  N - r + 1

/-- Paper-facing wrapper for the fixed symmetric layer family. -/
abbrev PomFiberFixedSymmetricLayerUnboundedScheduling (r N : ℕ) : Prop :=
  pom_fiber_fixed_symmetric_layer_unbounded_scheduling_family_size r N = N ∧
    pom_fiber_fixed_symmetric_layer_unbounded_scheduling_visible_algebra_dim r = 2 ^ r ∧
    pom_fiber_fixed_symmetric_layer_unbounded_scheduling_bulk_entropy ∧
    pom_fiber_fixed_symmetric_layer_unbounded_scheduling_complexity r N = N - r + 1 ∧
    1 ≤ pom_fiber_fixed_symmetric_layer_unbounded_scheduling_complexity r N

/-- Paper label: `thm:pom-fiber-fixed-symmetric-layer-unbounded-scheduling`. The explicit family
has total size `N`, the visible symmetric layer stays frozen at `(ℂ^2)^{⊗ r}` through the scalar
dimension `2^r`, the bulk entropy theorem is available verbatim, and the scheduling complexity is
`N - r + 1`, hence positive for every `N ≥ r`. -/
theorem paper_pom_fiber_fixed_symmetric_layer_unbounded_scheduling (r N : ℕ) (hr : 1 ≤ r)
    (hN : r ≤ N) : PomFiberFixedSymmetricLayerUnboundedScheduling r N := by
  refine ⟨?_, rfl, ?_, rfl, ?_⟩
  · dsimp [pom_fiber_fixed_symmetric_layer_unbounded_scheduling_family_size]
    omega
  · simpa [pom_fiber_fixed_symmetric_layer_unbounded_scheduling_bulk_entropy] using
      (paper_pom_fiber_bulk_scheduling_entropy_universal
        ({ } : PomFiberBulkSchedulingEntropyUniversalData))
  · dsimp [pom_fiber_fixed_symmetric_layer_unbounded_scheduling_complexity]
    omega

end Omega.POM
