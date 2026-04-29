import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.OperatorAlgebra.CircuitSkFixedKSharpPComplete
import Omega.OperatorAlgebra.FoldQuantumChannelChoiCapacity

namespace Omega.OperatorAlgebra

/-- Scalar block model of the circuit `k`-collision projector: one block for each circuit fiber. -/
noncomputable def circuit_k_collision_projector_rank_sharpp_complete_projector_data {n : ℕ}
    (C : BoolCircuit n) (k : ℕ) : FoldQuantumChannelCollisionData where
  blockRanks :=
    (Finset.univ : Finset (BitVec n)).toList.map fun y => Fintype.card { a : BitVec n // C a = y }
  q := k

/-- Concrete wrapper for the circuit projector-rank formulation together with the existing
fixed-`k` sharpP package. -/
def circuit_k_collision_projector_rank_sharpp_complete_statement (k : ℕ) : Prop :=
  (∀ {n : ℕ} (C : BoolCircuit n),
      let D := circuit_k_collision_projector_rank_sharpp_complete_projector_data C k
      D.qCollisionProjectorIsProjection ∧
        D.qCollisionProjectorRank = circuit_sk_fixedk_sharpp_complete_collision_sum C k) ∧
    circuit_sk_fixedk_sharpp_complete_statement k

/-- Paper label: `cor:circuit-k-collision-projector-rank-sharpP-complete`. -/
def paper_circuit_k_collision_projector_rank_sharpp_complete (k : ℕ) (_hk : 2 ≤ k) :
    Prop :=
  circuit_k_collision_projector_rank_sharpp_complete_statement k

theorem circuit_k_collision_projector_rank_sharpp_complete_certified (k : ℕ) (hk : 2 ≤ k) :
    paper_circuit_k_collision_projector_rank_sharpp_complete k hk := by
  refine ⟨?_, paper_circuit_sk_fixedk_sharpp_complete k hk⟩
  intro n C
  let D := circuit_k_collision_projector_rank_sharpp_complete_projector_data C k
  have hProj := paper_op_algebra_fold_q_collision_projector_rank D
  refine ⟨hProj.1, ?_⟩
  calc
    D.qCollisionProjectorRank = D.sqMoment := hProj.2
    _ = circuit_sk_fixedk_sharpp_complete_collision_sum C k := by
      classical
      simp [D, circuit_k_collision_projector_rank_sharpp_complete_projector_data,
        FoldQuantumChannelCollisionData.sqMoment,
        circuit_sk_fixedk_sharpp_complete_collision_sum]

end Omega.OperatorAlgebra
