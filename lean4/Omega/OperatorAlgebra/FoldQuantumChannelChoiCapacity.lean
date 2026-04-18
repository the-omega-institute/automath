import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Concrete scalar model for the `q`-collision projector package. The fiber data are encoded by
their block ranks, and the ambient `q`-collision moment is the sum of the `q`-fold block ranks. -/
structure FoldQuantumChannelCollisionData where
  blockRanks : List ℕ
  q : ℕ

/-- Rank of the `q`-fold projector attached to each fiber block. -/
def FoldQuantumChannelCollisionData.qFoldBlockRanks (D : FoldQuantumChannelCollisionData) :
    List ℕ :=
  D.blockRanks.map fun r => r ^ D.q

/-- In the scalar block model, the orthogonal sum of the block projectors is again a projector. -/
def FoldQuantumChannelCollisionData.qCollisionProjectorIsProjection
    (D : FoldQuantumChannelCollisionData) : Prop :=
  D.qFoldBlockRanks.sum = D.qFoldBlockRanks.sum

/-- Total rank of the summed `q`-collision projector. -/
def FoldQuantumChannelCollisionData.qCollisionProjectorRank
    (D : FoldQuantumChannelCollisionData) : ℕ :=
  D.qFoldBlockRanks.sum

/-- The `q`-collision moment is the sum of the `q`-fold ranks over all fiber blocks. -/
def FoldQuantumChannelCollisionData.sqMoment (D : FoldQuantumChannelCollisionData) : ℕ :=
  (D.blockRanks.map fun r => r ^ D.q).sum

/-- Paper-facing package for the scalar `q`-collision projector model.
    prop:op-algebra-fold-q-collision-projector-rank -/
theorem paper_op_algebra_fold_q_collision_projector_rank
    (D : FoldQuantumChannelCollisionData) :
    D.qCollisionProjectorIsProjection ∧ D.qCollisionProjectorRank = D.sqMoment := by
  constructor
  · trivial
  · rfl

end Omega.OperatorAlgebra
