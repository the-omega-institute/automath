import Omega.Conclusion.FoldNormalizerCharactersCompletelyStratified
import Omega.Conclusion.QfoldChannelChoiRankEqualsQcollision
import Omega.Conclusion.FixedQCollisionChoiRankSharppComplete
import Omega.Conclusion.SingleCollapseChoiRankSharppPersists

open scoped BigOperators
open Omega.Conclusion

/-- Paper label: `thm:conclusion-parity-poor-choi-rank-rich-orthogonal`. -/
theorem paper_conclusion_parity_poor_choi_rank_rich_orthogonal
    (layers : Finset (Nat × Nat)) (hpos : ∀ dn ∈ layers, 1 <= dn.1)
    {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X] (fold : Ω -> X)
    (q n sat s choiRank : Nat) (hq : 2 <= q)
    (D : conclusion_fixed_q_collision_choi_rank_sharpp_complete_Data) (hs : s = 2 * sat)
    (hRank : choiRank = s ^ q + (2 ^ (n + 1) - s))
    (hRecover :
      ∀ t,
        t % 2 = 0 ->
          t <= 2 ^ (n + 1) -> t ^ q + (2 ^ (n + 1) - t) = choiRank -> t = s) :
    (exists alpha,
        alpha = Finset.sum layers
          (fun dn => (Omega.OperatorAlgebra.foldWreathCharacterBasis dn.1 dn.2).card) ∧
          Finset.prod layers
            (fun dn => Omega.OperatorAlgebra.foldWreathAbelianizationOrder dn.1 dn.2) =
            2 ^ alpha) ∧
      conclusion_qfold_channel_choi_rank_equals_qcollision_statement fold q ∧
        conclusion_fixed_q_collision_choi_rank_sharpp_complete_Conclusion D ∧
          (exists recovered : Nat, recovered = sat ∧ s = 2 * recovered) := by
  constructor
  · exact paper_conclusion_fold_normalizer_characters_completely_stratified layers hpos
  constructor
  · exact conclusion_qfold_channel_choi_rank_equals_qcollision_verified fold q
  constructor
  · exact paper_conclusion_fixed_q_collision_choi_rank_sharpp_complete D
  · exact paper_conclusion_single_collapse_choi_rank_sharpp_persists
      q n sat s choiRank hq hs hRank hRecover
