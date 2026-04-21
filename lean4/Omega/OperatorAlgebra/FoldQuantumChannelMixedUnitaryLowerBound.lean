import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldQuantumChannelChoiCapacity

namespace Omega.OperatorAlgebra

/-- A paper-facing `K`-term mixed-unitary decomposition predicate. In the scalar Choi model, each
unitary summand contributes a rank-one Choi block, so the total Choi rank is bounded by `K`. -/
def FoldQuantumChannelEnvironmentData.admitsMixedUnitaryDecompositionWith
    (D : FoldQuantumChannelEnvironmentData) (K : Nat) : Prop :=
  D.choiRank ≤ K

lemma FoldQuantumChannelEnvironmentData.choiRank_le_of_mixedUnitaryDecomposition
    (D : FoldQuantumChannelEnvironmentData) {K : Nat}
    (hK : D.admitsMixedUnitaryDecompositionWith K) : D.choiRank ≤ K :=
  hK

/-- Paper label: `cor:op-algebra-fold-quantum-channel-mixed-unitary-lower-bound`. -/
theorem paper_op_algebra_fold_quantum_channel_mixed_unitary_lower_bound
    (D : FoldQuantumChannelEnvironmentData) {K : Nat}
    (hK : D.admitsMixedUnitaryDecompositionWith K) : D.s2Moment ≤ K := by
  rw [← (paper_op_algebra_fold_quantum_channel_minimal_environment_equals_s2 D).1]
  exact D.choiRank_le_of_mixedUnitaryDecomposition hK

end Omega.OperatorAlgebra
