import Mathlib.Data.Fintype.Basic
import Omega.OperatorAlgebra.FoldQuantumChannelChoiCapacity

namespace Omega.Conclusion

open Omega.OperatorAlgebra

/-- Fiber cardinality of the finite fold at a chosen output point. -/
noncomputable def conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card
    {Omega X : Type*} [Fintype Omega] [Fintype X] (fold : Omega → X) (x : X) : ℕ :=
  by
    classical
    exact Fintype.card {ω : Omega // fold ω = x}

/-- Block ranks of the folded channel, recorded over the finite output alphabet. -/
noncomputable def conclusion_qfold_channel_choi_rank_equals_qcollision_block_ranks
    {Omega X : Type*} [Fintype Omega] [Fintype X] (fold : Omega → X) : List ℕ := by
  classical
  exact (Finset.univ : Finset X).toList.map
    (conclusion_qfold_channel_choi_rank_equals_qcollision_fiber_card fold)

/-- The scalar direct-sum model attached to the `q`-fold channel. -/
noncomputable def conclusion_qfold_channel_choi_rank_equals_qcollision_data
    {Omega X : Type*} [Fintype Omega] [Fintype X] (fold : Omega → X) (q : ℕ) :
    FoldQuantumChannelCollisionData :=
  { blockRanks := conclusion_qfold_channel_choi_rank_equals_qcollision_block_ranks fold
    q := q }

/-- The `q`-fold Choi-rank package: the orthogonal block projector is a projection and its rank is
the `q`-collision moment computed from the fiber sizes. -/
def conclusion_qfold_channel_choi_rank_equals_qcollision_statement
    {Omega X : Type*} [Fintype Omega] [Fintype X] (fold : Omega → X) (q : ℕ) : Prop :=
  2 ≤ q →
    let D := conclusion_qfold_channel_choi_rank_equals_qcollision_data fold q
    D.qCollisionProjectorIsProjection ∧ D.qCollisionProjectorRank = D.sqMoment

/-- Verification theorem for the finite `q`-fold Choi-rank package. -/
theorem conclusion_qfold_channel_choi_rank_equals_qcollision_verified
    {Omega X : Type*} [Fintype Omega] [Fintype X] (fold : Omega → X) (q : ℕ) :
    conclusion_qfold_channel_choi_rank_equals_qcollision_statement fold q := by
  intro _hq
  let D := conclusion_qfold_channel_choi_rank_equals_qcollision_data fold q
  simpa [D] using paper_op_algebra_fold_q_collision_projector_rank D

/-- Paper label: `thm:conclusion-qfold-channel-choi-rank-equals-qcollision`. -/
def paper_conclusion_qfold_channel_choi_rank_equals_qcollision
    {Omega X : Type*} [Fintype Omega] [Fintype X] (fold : Omega → X) (q : ℕ) : Prop := by
  exact conclusion_qfold_channel_choi_rank_equals_qcollision_statement fold q

end Omega.Conclusion
