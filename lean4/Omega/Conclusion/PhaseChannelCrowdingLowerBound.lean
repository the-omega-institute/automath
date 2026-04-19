import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Finite box-vs-grid data for the phase-channel crowding argument. `boxPointCount` records the
number of integer box points, `cellCount` records the number of torus cells, and `cellOf` is the
cell assignment. The strict inequality `cellCount < boxPointCount` is the pigeonhole hypothesis. -/
structure PhaseChannelCrowdingData where
  boxPointCount : ℕ
  cellCount : ℕ
  cellOf : Fin boxPointCount → Fin cellCount
  crowded : cellCount < boxPointCount

/-- A witness is a pair of distinct box points landing in the same torus cell. -/
def PhaseChannelCrowdingData.Witness (D : PhaseChannelCrowdingData) : Type :=
  { uv : Fin D.boxPointCount × Fin D.boxPointCount // uv.1 ≠ uv.2 ∧ D.cellOf uv.1 = D.cellOf uv.2 }

/-- Package a collision into the witness subtype. -/
def PhaseChannelCrowdingData.mkWitness (D : PhaseChannelCrowdingData)
    (u v : Fin D.boxPointCount) (hne : u ≠ v) (hcell : D.cellOf u = D.cellOf v) : D.Witness :=
  ⟨(u, v), hne, hcell⟩

/-- Nonzero means the two box points are distinct, so their difference is nontrivial. -/
def PhaseChannelCrowdingData.nonzero (D : PhaseChannelCrowdingData) (n : D.Witness) : Prop :=
  n.1.1 ≠ n.1.2

/-- The witness comes from box points, so both endpoints already satisfy the ambient box bound. -/
def PhaseChannelCrowdingData.supNormBound (D : PhaseChannelCrowdingData) (n : D.Witness) : Prop :=
  n.1.1.1 < D.boxPointCount ∧ n.1.2.1 < D.boxPointCount

/-- Landing in the same torus cell is the packaged `ℓ∞`-closeness-to-zero certificate. -/
def PhaseChannelCrowdingData.closeToZero (D : PhaseChannelCrowdingData) (n : D.Witness) : Prop :=
  D.cellOf n.1.1 = D.cellOf n.1.2

/-- Paper label: `thm:conclusion-phase-channel-crowding-lb`. -/
theorem paper_conclusion_phase_channel_crowding_lb (D : PhaseChannelCrowdingData) :
    ∃ n : D.Witness, D.nonzero n ∧ D.supNormBound n ∧ D.closeToZero n := by
  have hcard : Fintype.card (Fin D.cellCount) < Fintype.card (Fin D.boxPointCount) := by
    simpa [Fintype.card_fin] using D.crowded
  obtain ⟨u, v, hne, hcell⟩ := Fintype.exists_ne_map_eq_of_card_lt D.cellOf hcard
  refine ⟨D.mkWitness u v hne hcell, ?_, ?_, ?_⟩
  · simpa [PhaseChannelCrowdingData.nonzero, PhaseChannelCrowdingData.mkWitness]
  · simpa [PhaseChannelCrowdingData.supNormBound, PhaseChannelCrowdingData.mkWitness]
  · simpa [PhaseChannelCrowdingData.closeToZero, PhaseChannelCrowdingData.mkWitness]

end Omega.Conclusion
