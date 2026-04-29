import Omega.SPG.CoordinateBundleScreenCount

namespace Omega.Conclusion

/-- The SPG screen-component closed form already counts one exterior component plus one component
for each complement-coordinate slab, so subtracting the exterior component recovers the exact slab
count.
    thm:conclusion-coordinate-bundle-kernel-slab-decomposition -/
theorem paper_conclusion_coordinate_bundle_kernel_slab_decomposition (m n s : ℕ) :
    Omega.SPG.CoordinateBundleScreenCount.screenComponentCount m n s - 1 = 2 ^ (m * (n - s)) := by
  simp [Omega.SPG.CoordinateBundleScreenCount.screenComponentCount]

end Omega.Conclusion
