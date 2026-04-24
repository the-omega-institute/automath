import Mathlib.Tactic
import Omega.Folding.MomentTriple
import Omega.OperatorAlgebra.FoldQuantumChannelChoiCapacity

namespace Omega.OperatorAlgebra

/-- Paper label: `cor:op-algebra-fold-quantum-channel-minenv-equals-sphere-partition-function`.
Once the folded quantum channel and the sphere partition function are both identified with the same
second collision moment `S₂(m)`, the two quantities agree by transitivity. -/
theorem paper_op_algebra_fold_quantum_channel_minenv_equals_sphere_partition_function
    (D : FoldQuantumChannelEnvironmentData) (m : ℕ)
    (hSphere : D.s2Moment = Omega.momentSum 2 m) :
    D.minEnvironmentDim = ∑ x : Omega.X m, (Omega.X.fiberMultiplicity x) ^ 2 := by
  rw [(paper_op_algebra_fold_quantum_channel_minimal_environment_equals_s2 D).2.2]
  rw [hSphere, Omega.paper_def_s2]

end Omega.OperatorAlgebra
