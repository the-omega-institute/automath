import Mathlib.Tactic
import Omega.SPG.CoordinateBundleScreenCount

namespace Omega.Conclusion

/-- Concrete data for the coordinate-bundle exactification/hitting equivalence. The number
`hitLayerCount` records the distinct exterior slabs hit by the chosen boundary set. -/
structure conclusion_coordinate_bundle_exactification_partition_matroid_data where
  m : ℕ
  n : ℕ
  s : ℕ
  hitLayerCount : ℕ
  hitLayerCount_le :
    hitLayerCount ≤ 2 ^ (m * (n - s))

namespace conclusion_coordinate_bundle_exactification_partition_matroid_data

/-- Number of outer boundary slabs in the coordinate bundle. -/
def conclusion_coordinate_bundle_exactification_partition_matroid_layerCount
    (D : conclusion_coordinate_bundle_exactification_partition_matroid_data) : ℕ :=
  2 ^ (D.m * (D.n - D.s))

/-- Residual free kernel rank after hitting the recorded number of slabs. -/
def conclusion_coordinate_bundle_exactification_partition_matroid_residualKernelRank
    (D : conclusion_coordinate_bundle_exactification_partition_matroid_data) : ℕ :=
  (Omega.SPG.CoordinateBundleScreenCount.screenComponentCount D.m D.n D.s - D.hitLayerCount) - 1

/-- Exactification means the residual kernel rank has vanished. -/
def exactifies (D : conclusion_coordinate_bundle_exactification_partition_matroid_data) : Prop :=
  D.conclusion_coordinate_bundle_exactification_partition_matroid_residualKernelRank = 0

/-- Hitting every partition block means the number of hit slabs equals the slab count. -/
def hits_every_layer
    (D : conclusion_coordinate_bundle_exactification_partition_matroid_data) : Prop :=
  D.hitLayerCount =
    D.conclusion_coordinate_bundle_exactification_partition_matroid_layerCount

/-- Paper-facing equivalence between exactification and the partition-matroid hitting condition. -/
def exactifies_iff_hits_every_layer
    (D : conclusion_coordinate_bundle_exactification_partition_matroid_data) : Prop :=
  D.exactifies ↔ D.hits_every_layer

end conclusion_coordinate_bundle_exactification_partition_matroid_data

open conclusion_coordinate_bundle_exactification_partition_matroid_data

/-- Paper label: `thm:conclusion-coordinate-bundle-exactification-partition-matroid`. The
screen-count closed form reduces exactification to the equation `L - t = 0`, which is equivalent
to having hit all `L` slabs. -/
theorem paper_conclusion_coordinate_bundle_exactification_partition_matroid
    (D : conclusion_coordinate_bundle_exactification_partition_matroid_data) :
    D.exactifies_iff_hits_every_layer := by
  rw [exactifies_iff_hits_every_layer, exactifies, hits_every_layer,
    conclusion_coordinate_bundle_exactification_partition_matroid_residualKernelRank,
    conclusion_coordinate_bundle_exactification_partition_matroid_layerCount]
  rw [Omega.SPG.CoordinateBundleScreenCount.screenComponentCount_eq]
  have hhit : D.hitLayerCount ≤ 2 ^ (D.m * (D.n - D.s)) := D.hitLayerCount_le
  have hlayers_pos : 0 < 2 ^ (D.m * (D.n - D.s)) := Nat.pow_pos (by omega)
  omega

end Omega.Conclusion
