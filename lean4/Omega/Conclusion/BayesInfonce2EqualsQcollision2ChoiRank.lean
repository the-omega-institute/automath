import Omega.Conclusion.QfoldChannelChoiRankEqualsQcollision

namespace Omega.Conclusion

/-- Paper-facing binary specialization of the q-fold Choi-rank/q-collision package.
    cor:conclusion-bayes-infonce2-equals-qcollision2-choi-rank -/
theorem paper_conclusion_bayes_infonce2_equals_qcollision2_choi_rank
    {Ω X : Type*} [Fintype Ω] [Fintype X] (fold : Ω → X) :
    let D := Omega.Conclusion.conclusion_qfold_channel_choi_rank_equals_qcollision_data fold 2
    D.qCollisionProjectorIsProjection ∧ D.qCollisionProjectorRank = D.sqMoment := by
  exact (conclusion_qfold_channel_choi_rank_equals_qcollision_verified fold 2)
    (by decide : 2 ≤ 2)

end Omega.Conclusion
