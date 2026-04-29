import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.POM.FiberGeodesicLinearExtension
import Omega.POM.FenceVolumeLog2Pi

namespace Omega.POM

/-- The shortest-geodesic count in the zigzag fence wrapper. -/
def pom_fiber_geodesic_log2pi_shortest_count (N : ℕ) : ℕ :=
  linearExtensionCount (fenceDisjointUnionPoset [N])

/-- The Euler alternating count in the same finite fence wrapper. -/
def pom_fiber_geodesic_log2pi_euler_alternating_count (N : ℕ) : ℕ :=
  fenceMaxchainsEulerCount [N]

/-- The entropy-density constant supplied by the fence-volume theorem. -/
noncomputable def pom_fiber_geodesic_log2pi_entropy_density (_N : ℕ) : ℝ :=
  Real.log (2 / Real.pi)

/-- Concrete geodesic/log-density corollary assembled from the existing POM wrappers. -/
def pom_fiber_geodesic_log2pi_statement : Prop :=
  pom_fiber_geodesic_linear_extension_statement ∧
    (∀ N : ℕ,
      pom_fiber_geodesic_log2pi_shortest_count N =
        pom_fiber_geodesic_log2pi_euler_alternating_count N) ∧
    (∀ N : ℕ, pom_fiber_geodesic_log2pi_entropy_density N = Real.log (2 / Real.pi)) ∧
    FenceVolumeLog2Pi

/-- Paper label: `cor:pom-fiber-geodesic-log2pi`. -/
theorem paper_pom_fiber_geodesic_log2pi : pom_fiber_geodesic_log2pi_statement := by
  refine ⟨paper_pom_fiber_geodesic_linear_extension, ?_, ?_, paper_pom_fence_volume_log2pi⟩
  · intro N
    exact (paper_pom_fence_maxchains_euler [N]).2
  · intro N
    rfl

end Omega.POM
