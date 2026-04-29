import Mathlib.Tactic
import Omega.POM.MicrocanonicalFoldClassCount

namespace Omega.POM

open scoped BigOperators

/-! Concrete counting package for the microcanonical fold-query lower bound. -/

structure MicrocanonicalFoldQueryLowerBoundData where
  X : Type
  instFintypeX : Fintype X
  instDecidableEqX : DecidableEq X
  fiberProfile : X → ℕ
  queryCount : ℕ
  requiredQueryLowerBound : ℕ
  paper_label_pom_microcanonical_fold_query_lower_bound_alphabet_card_two :
    2 ≤ Fintype.card X
  paper_label_pom_microcanonical_fold_query_lower_bound_transcript_bound :
    microcanonicalFoldClassCount fiberProfile ≤ (Fintype.card X) ^ queryCount
  paper_label_pom_microcanonical_fold_query_lower_bound_pigeonhole_witness :
    (Fintype.card X) ^ requiredQueryLowerBound < microcanonicalFoldClassCount fiberProfile

attribute [instance] MicrocanonicalFoldQueryLowerBoundData.instFintypeX
attribute [instance] MicrocanonicalFoldQueryLowerBoundData.instDecidableEqX

/-- Any lower-bound witness of the form `|X|^r < |Fold(d)|` is bounded above by every query budget
whose transcript space already covers `|Fold(d)|`. -/
theorem paper_pom_microcanonical_fold_query_lower_bound
    (D : MicrocanonicalFoldQueryLowerBoundData) : D.requiredQueryLowerBound <= D.queryCount := by
  have halphabet_gt_one : 1 < Fintype.card D.X := by
    exact lt_of_lt_of_le (by decide : 1 < 2)
      D.paper_label_pom_microcanonical_fold_query_lower_bound_alphabet_card_two
  by_contra hnot
  have hq : D.queryCount < D.requiredQueryLowerBound := by
    omega
  have hpow :
      (Fintype.card D.X) ^ D.queryCount < (Fintype.card D.X) ^ D.requiredQueryLowerBound := by
    exact Nat.pow_lt_pow_right halphabet_gt_one hq
  have hchain :
      (Fintype.card D.X) ^ D.queryCount < (Fintype.card D.X) ^ D.queryCount := by
    exact lt_of_lt_of_le hpow
      (lt_of_lt_of_le
        D.paper_label_pom_microcanonical_fold_query_lower_bound_pigeonhole_witness
        D.paper_label_pom_microcanonical_fold_query_lower_bound_transcript_bound).le
  exact (lt_irrefl _ hchain).elim

end Omega.POM
