import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-hook-channel-implies-partition-gap-closed`. -/
theorem paper_pom_hook_channel_implies_partition_gap_closed (partitionGap : ℝ)
    (hookChannelNonzero : Prop) (hNonneg : 0 ≤ partitionGap)
    (hStrictGapKillsHook : 0 < partitionGap → ¬hookChannelNonzero) :
    hookChannelNonzero → partitionGap = 0 := by
  intro hHook
  have hnot_pos : ¬0 < partitionGap := by
    intro hPos
    exact hStrictGapKillsHook hPos hHook
  have hnonpos : partitionGap ≤ 0 := le_of_not_gt hnot_pos
  linarith

end Omega.POM
