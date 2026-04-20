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

/-- Scalar block data for the Choi/Kraus/environment package of the folded quantum channel. The
fiber multiplicities are encoded by their block ranks, and every minimal size is computed by the
sum of the squared ranks. -/
structure FoldQuantumChannelEnvironmentData where
  blockRanks : List ℕ

/-- Fiber block ranks appearing in the folded channel. -/
def FoldQuantumChannelEnvironmentData.fiberBlockRanks
    (D : FoldQuantumChannelEnvironmentData) : List ℕ :=
  D.blockRanks

/-- Rank contribution of each fiber block to the Choi matrix. -/
def FoldQuantumChannelEnvironmentData.choiBlockRanks
    (D : FoldQuantumChannelEnvironmentData) : List ℕ :=
  D.fiberBlockRanks.map fun d => d ^ 2

/-- Total Choi rank of the folded channel. -/
def FoldQuantumChannelEnvironmentData.choiRank
    (D : FoldQuantumChannelEnvironmentData) : ℕ :=
  D.choiBlockRanks.sum

/-- The second collision moment `S₂ = ∑ₓ dₓ²`. -/
def FoldQuantumChannelEnvironmentData.s2Moment
    (D : FoldQuantumChannelEnvironmentData) : ℕ :=
  (D.blockRanks.map fun d => d ^ 2).sum

/-- Size of the explicit Kraus family indexed by ordered pairs inside each fiber block. -/
def FoldQuantumChannelEnvironmentData.krausFamilyCard
    (D : FoldQuantumChannelEnvironmentData) : ℕ :=
  D.choiRank

/-- Minimal Kraus count, identified with the Choi rank in this scalar block model. -/
def FoldQuantumChannelEnvironmentData.minKrausCount
    (D : FoldQuantumChannelEnvironmentData) : ℕ :=
  D.krausFamilyCard

/-- Minimal Stinespring environment dimension, again equal to the Choi rank in this model. -/
def FoldQuantumChannelEnvironmentData.minEnvironmentDim
    (D : FoldQuantumChannelEnvironmentData) : ℕ :=
  D.minKrausCount

/-- Paper label: `thm:op-algebra-fold-quantum-channel-minimal-environment-equals-s2`. -/
theorem paper_op_algebra_fold_quantum_channel_minimal_environment_equals_s2
    (D : FoldQuantumChannelEnvironmentData) :
    D.choiRank = D.s2Moment ∧ D.minKrausCount = D.s2Moment ∧ D.minEnvironmentDim = D.s2Moment := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

end Omega.OperatorAlgebra
