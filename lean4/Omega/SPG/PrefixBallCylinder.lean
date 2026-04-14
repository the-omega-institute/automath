import Omega.SPG.PrefixMetric

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the prefix-ball/cylinder identification.
    lem:prefix-ball-cylinder -/
theorem paper_scan_projection_address_prefix_ball_cylinder_seeds
    {m : Nat} (w : Word m) {ξ : OmegaInfinity} (hξ : ξ ∈ cylinderWord w) :
    cylinderWord w = {η : OmegaInfinity | prefixDist η ξ ≤ (1 / 2 : ℝ) ^ m} := by
  have hprefix : prefixWord ξ m = w := by
    simpa [cylinderWord] using hξ
  calc
    cylinderWord w = cylinderWord (prefixWord ξ m) := by rw [hprefix]
    _ = prefixBall ξ m := by
      symm
      exact prefixBall_eq_cylinderWord ξ m
    _ = {η : OmegaInfinity | prefixDist η ξ ≤ (1 / 2 : ℝ) ^ m} :=
      prefixBall_eq_closedBall ξ m

/-- Packaged form of the prefix-ball/cylinder identification.
    lem:prefix-ball-cylinder -/
theorem paper_scan_projection_address_prefix_ball_cylinder_package
    {m : Nat} (w : Word m) {ξ : OmegaInfinity} (hξ : ξ ∈ cylinderWord w) :
    cylinderWord w = {η : OmegaInfinity | prefixDist η ξ ≤ (1 / 2 : ℝ) ^ m} :=
  paper_scan_projection_address_prefix_ball_cylinder_seeds w hξ

end Omega.SPG
