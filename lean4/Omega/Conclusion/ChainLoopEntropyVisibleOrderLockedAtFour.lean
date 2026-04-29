import Mathlib.Tactic
import Omega.Conclusion.ChainLoopEntropySecondDifferenceDefectExpansion

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Concrete weak-coherence package for the quartic visible-order corollary. -/
structure conclusion_chain_loop_entropy_visible_order_locked_at_four_data where
  base : conclusion_chain_loop_entropy_second_difference_defect_expansion_data
  eps : ℝ
  quarticLeadingCoeff : ℝ
  quarticRemainderCoeff : ℝ
  etaLeading : ℕ → ℝ
  eta_quadratic_scale :
    ∀ j, 3 ≤ j → j ≤ base.kappa →
      conclusion_chain_loop_entropy_second_difference_defect_expansion_eta base j =
        eps ^ 2 * etaLeading j
  finite_quadratic_sum_scale :
    conclusion_chain_loop_entropy_second_difference_defect_expansion_quadraticSum base =
      quarticLeadingCoeff * eps ^ 4
  remainder_scale :
    base.defectRemainder = quarticRemainderCoeff * eps ^ 4
  nonvanishingIndex : ℕ
  nonvanishingIndex_low : 3 ≤ nonvanishingIndex
  nonvanishingIndex_high : nonvanishingIndex ≤ base.kappa
  etaLeading_nonzero : etaLeading nonvanishingIndex ≠ 0
  quarticLeadingCoeff_nonzero : quarticLeadingCoeff ≠ 0

/-- The loop entropy has quartic leading scale, with recorded weak-coherence and nonvanishing
witness data. -/
def conclusion_chain_loop_entropy_visible_order_locked_at_four_statement
    (D : conclusion_chain_loop_entropy_visible_order_locked_at_four_data) : Prop :=
  conclusion_chain_loop_entropy_second_difference_defect_expansion_loopEntropy D.base =
      (D.quarticLeadingCoeff + D.quarticRemainderCoeff) * D.eps ^ 4 ∧
    (∀ j, 3 ≤ j → j ≤ D.base.kappa →
      conclusion_chain_loop_entropy_second_difference_defect_expansion_eta D.base j =
        D.eps ^ 2 * D.etaLeading j) ∧
    (∃ j, 3 ≤ j ∧ j ≤ D.base.kappa ∧ D.etaLeading j ≠ 0) ∧
    D.quarticLeadingCoeff ≠ 0 ∧
    D.base.weak_coherent_loop_entropy_expansion

/-- Paper label: `cor:conclusion-chain-loop-entropy-visible-order-locked-at-four`. -/
theorem paper_conclusion_chain_loop_entropy_visible_order_locked_at_four
    (D : conclusion_chain_loop_entropy_visible_order_locked_at_four_data) :
    conclusion_chain_loop_entropy_visible_order_locked_at_four_statement D := by
  refine ⟨?_, D.eta_quadratic_scale, ?_, D.quarticLeadingCoeff_nonzero, ?_⟩
  · rw [conclusion_chain_loop_entropy_second_difference_defect_expansion_loopEntropy,
      D.finite_quadratic_sum_scale, D.remainder_scale]
    ring
  · exact
      ⟨D.nonvanishingIndex, D.nonvanishingIndex_low, D.nonvanishingIndex_high,
        D.etaLeading_nonzero⟩
  · exact paper_conclusion_chain_loop_entropy_second_difference_defect_expansion D.base

end

end Omega.Conclusion
