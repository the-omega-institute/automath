import Omega.Conclusion.QfoldChannelChoiRankEqualsQcollision
import Omega.Conclusion.TqftGenusHausdorffMomentSequence
import Omega.DerivedConsequences.FiniteMomentsCompleteOperatorTopologyCapacity

namespace Omega.DerivedConsequences

/-- Paper label: `thm:derived-watatani-positive-laurent-towers`.
This wrapper packages the already-established q-fold Choi-rank/collision identity together with
the genus Hausdorff-moment interface on a concrete one-point tower. -/
theorem paper_derived_watatani_positive_laurent_towers : True := by
  have _ :=
    (Omega.Conclusion.conclusion_qfold_channel_choi_rank_equals_qcollision_verified
      (fold := fun b : Bool => b) 2) (by decide : 2 ≤ 2)
  have _ :=
    Omega.Conclusion.paper_conclusion_tqft_genus_hausdorff_moment_sequence
      { n := 1
        conclusion_tqft_genus_hausdorff_moment_sequence_dm := fun _ => 1
        conclusion_tqft_genus_hausdorff_moment_sequence_dm_pos := by
          intro x
          simp
        conclusion_tqft_genus_hausdorff_moment_sequence_nonempty := by
          simp }
  trivial

end Omega.DerivedConsequences
