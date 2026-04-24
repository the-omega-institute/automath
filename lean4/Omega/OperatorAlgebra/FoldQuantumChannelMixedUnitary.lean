import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldQuantumChannelMixedUnitaryLowerBound

namespace Omega.OperatorAlgebra

/-- In the scalar block model, the explicit mixed-unitary twirl is indexed by the same ordered
pair data as the Kraus family, so its cardinality is `∑ₓ dₓ² = S₂`. -/
def FoldQuantumChannelEnvironmentData.explicitMixedUnitaryCard
    (D : FoldQuantumChannelEnvironmentData) : Nat :=
  D.krausFamilyCard

/-- Paper label: `prop:op-algebra-fold-quantum-channel-mixed-unitary`. -/
theorem paper_op_algebra_fold_quantum_channel_mixed_unitary
    (D : FoldQuantumChannelEnvironmentData) :
    D.admitsMixedUnitaryDecompositionWith D.explicitMixedUnitaryCard ∧
      D.explicitMixedUnitaryCard = D.s2Moment := by
  constructor
  · show D.choiRank ≤ D.explicitMixedUnitaryCard
    simp [FoldQuantumChannelEnvironmentData.explicitMixedUnitaryCard,
      FoldQuantumChannelEnvironmentData.krausFamilyCard]
  · rw [FoldQuantumChannelEnvironmentData.explicitMixedUnitaryCard,
      FoldQuantumChannelEnvironmentData.krausFamilyCard]
    exact (paper_op_algebra_fold_quantum_channel_minimal_environment_equals_s2 D).1

end Omega.OperatorAlgebra
