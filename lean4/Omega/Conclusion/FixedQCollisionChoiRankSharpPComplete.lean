import Omega.Conclusion.QfoldChannelChoiRankEqualsQcollision
import Omega.OperatorAlgebra.CircuitKCollisionProjectorRankSharpPComplete

namespace Omega.Conclusion

open Omega.OperatorAlgebra

/-- Concrete fixed-`q` input package for the collision-moment/Choi-rank completeness statement. -/
structure conclusion_fixed_q_collision_choi_rank_sharpp_complete_Data where
  q : ℕ
  hq : 2 ≤ q

/-- The q-fold finite Choi-rank block model attached to a fold map. -/
noncomputable def conclusion_fixed_q_collision_choi_rank_sharpp_complete_fold_data
    {Ω X : Type*} [Fintype Ω] [Fintype X]
    (D : conclusion_fixed_q_collision_choi_rank_sharpp_complete_Data) (fold : Ω → X) :
    FoldQuantumChannelCollisionData :=
  conclusion_qfold_channel_choi_rank_equals_qcollision_data fold D.q

/-- Fixed-`q` Choi-rank completeness is the conjunction of the finite q-fold rank identity and the
existing fixed-k #P-completeness certificate for collision sums. -/
def conclusion_fixed_q_collision_choi_rank_sharpp_complete_Conclusion
    (D : conclusion_fixed_q_collision_choi_rank_sharpp_complete_Data) : Prop :=
  (∀ {Ω X : Type*} [Fintype Ω] [Fintype X] (fold : Ω → X),
      let Q := conclusion_fixed_q_collision_choi_rank_sharpp_complete_fold_data D fold
      Q.qCollisionProjectorIsProjection ∧ Q.qCollisionProjectorRank = Q.sqMoment) ∧
    circuit_k_collision_projector_rank_sharpp_complete_statement D.q

/-- Paper label: `thm:conclusion-fixed-q-collision-choi-rank-sharpp-complete`. -/
theorem paper_conclusion_fixed_q_collision_choi_rank_sharpp_complete
    (D : conclusion_fixed_q_collision_choi_rank_sharpp_complete_Data) :
    conclusion_fixed_q_collision_choi_rank_sharpp_complete_Conclusion D := by
  refine ⟨?_, circuit_k_collision_projector_rank_sharpp_complete_certified D.q D.hq⟩
  intro Ω X _ _ fold
  simpa [conclusion_fixed_q_collision_choi_rank_sharpp_complete_fold_data]
    using conclusion_qfold_channel_choi_rank_equals_qcollision_verified fold D.q D.hq

end Omega.Conclusion
