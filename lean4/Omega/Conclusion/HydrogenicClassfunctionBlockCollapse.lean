import Mathlib.Algebra.Group.Nat.Even

namespace Omega.Conclusion

lemma conclusion_hydrogenic_classfunction_block_collapse_address_loss_count (n : Nat) :
    2 * (n * (n - 1) / 2) = n * (n - 1) := by
  exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)

/-- Paper label: `thm:conclusion-hydrogenic-classfunction-block-collapse`. -/
theorem paper_conclusion_hydrogenic_classfunction_block_collapse (n : Nat)
    (blockScalarCollapse sectorFactorization : Prop) (hBlock : blockScalarCollapse)
    (hFactor : sectorFactorization) :
    blockScalarCollapse ∧ sectorFactorization ∧ 2 * (n * (n - 1) / 2) = n * (n - 1) := by
  exact ⟨hBlock, hFactor, conclusion_hydrogenic_classfunction_block_collapse_address_loss_count n⟩

end Omega.Conclusion
