import Mathlib.Tactic
import Omega.Conclusion.CompressionLadderSpin10

namespace Omega.GU

/-- Chapter-local package for the `so(10)` central `2`-torsion collapse audit. The three-axis
boundary audit starts from rank `3`, while connected `Spin(10)`-type envelopes contribute at most
rank `1` of central `2`-torsion. -/
structure So10TwoTorsionCentralCollapseData where
  auditCentralRank : ℕ
  connectedCentralTwoTorsionRank : ℕ
  auditCentralRank_eq_three : auditCentralRank = 3
  connectedCentralTwoTorsionRank_le_one : connectedCentralTwoTorsionRank ≤ 1

/-- Paper-facing impossibility of retaining rank-`3` central `2`-torsion inside a connected
`so(10)`-type envelope. -/
def So10TwoTorsionCentralCollapseData.no_rank3_central_2torsion
    (h : So10TwoTorsionCentralCollapseData) : Prop :=
  ¬ 3 ≤ h.connectedCentralTwoTorsionRank

/-- Paper-facing statement that at least two independent central `2`-torsion directions must be
lost when passing from the three-axis audit to a connected `so(10)`-type envelope. -/
def So10TwoTorsionCentralCollapseData.central_rank_drop_at_least_two
    (h : So10TwoTorsionCentralCollapseData) : Prop :=
  h.auditCentralRank - h.connectedCentralTwoTorsionRank ≥ 2

/-- A connected `so(10)`-type envelope cannot retain all three audited central `2`-torsion
directions; relative to the three-axis starting point, at least two directions collapse.
    thm:so10-2torsion-central-collapse-necessity -/
theorem paper_so10_2torsion_central_collapse_necessity
    (h : So10TwoTorsionCentralCollapseData) :
    h.no_rank3_central_2torsion ∧ h.central_rank_drop_at_least_two := by
  refine ⟨?_, ?_⟩
  · dsimp [So10TwoTorsionCentralCollapseData.no_rank3_central_2torsion]
    have := h.connectedCentralTwoTorsionRank_le_one
    omega
  · dsimp [So10TwoTorsionCentralCollapseData.central_rank_drop_at_least_two]
    rw [h.auditCentralRank_eq_three]
    have := h.connectedCentralTwoTorsionRank_le_one
    omega

end Omega.GU
