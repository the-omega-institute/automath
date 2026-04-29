import Mathlib.Tactic
import Omega.Conclusion.CoordinateBundleKernelSlabDecomposition
import Omega.SPG.CoordinateBundleScreenCount
import Omega.SPG.ScreenKernelConnectedComponents

namespace Omega.Conclusion

/-- Paper-facing residual-rank statement: after hitting `t` previously disjoint slabs from the
outer boundary family, the free screen-kernel rank drops from `L` to `L - t`. -/
def conclusion_coordinate_bundle_outer_boundary_residual_rank_statement
    (m n s : Nat) : Prop :=
  let L := 2 ^ (m * (n - s))
  ∀ t : Nat,
    t ≤ L →
      (Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n s - t) - 1 = L - t

/-- Paper label: `thm:conclusion-coordinate-bundle-outer-boundary-residual-rank`. The internal
screen starts with `L + 1` connected components, and each newly hit slab merges exactly one free
component with the exterior component, decreasing the residual kernel rank by one. -/
theorem paper_conclusion_coordinate_bundle_outer_boundary_residual_rank
    (m n s : Nat) : conclusion_coordinate_bundle_outer_boundary_residual_rank_statement m n s := by
  dsimp [conclusion_coordinate_bundle_outer_boundary_residual_rank_statement]
  let L := 2 ^ (m * (n - s))
  have hslabs :
      Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n s - 1 = L := by
    simpa [L] using paper_conclusion_coordinate_bundle_kernel_slab_decomposition m n s
  intro t ht
  have hcomponents :
      1 ≤ Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n s - t := by
    have hscreen :
        Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n s = L + 1 := by
      simp [L, Omega.SPG.CoordinateBundleScreenCount.screenComponentCount]
    omega
  have hfree :
      (Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n s - t) - 1 + 1 =
        Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n s - t := by
    exact Omega.SPG.ScreenKernelConnectedComponents.free_components_count
      (Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n s - t) hcomponents
  omega

end Omega.Conclusion
