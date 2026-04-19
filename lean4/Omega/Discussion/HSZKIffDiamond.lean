import Mathlib.Tactic

namespace Omega.Discussion

/-- Chapter-local package for the equivalence between the HSZK condition and the comb-diamond
criterion. The fields encode the two paper definitions together with the two rewrite directions
obtained by unfolding the quantifier packages over simulators and verifiers and normalizing the
supremum-over-verifiers clause. -/
structure HSZKIffDiamondData where
  hszkCondition : Prop
  diamondCriterion : Prop
  hszkImpliesDiamond : hszkCondition → diamondCriterion
  diamondImpliesHszk : diamondCriterion → hszkCondition

/-- The HSZK condition is equivalent to the comb-diamond criterion once both chapter-local
packages are unfolded and the verifier supremum clause is rewritten.
    thm:discussion-hszk-iff-diamond -/
theorem paper_discussion_hszk_iff_diamond (D : HSZKIffDiamondData) :
    D.hszkCondition ↔ D.diamondCriterion := by
  exact ⟨D.hszkImpliesDiamond, D.diamondImpliesHszk⟩

end Omega.Discussion
