import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.GoldenBiasSecondOrderUniqueness

open scoped goldenRatio

namespace Omega.Conclusion

/-- The two-atom completion moment functional for the balanced branch model. -/
def balancedTwoatomCompletionMoment (phi p : ℝ) (q : ℕ) : ℝ :=
  p + (1 - p) * phi ^ q

/-- The two admissible completion branches isolated by coefficient comparison in the paper. -/
def balancedTwoatomCompletionBranch (phi p kappa : ℝ) : Prop :=
  (p = (1 / 2 : ℝ) ∧ kappa = 4) ∨ (p = 1 / phi ∧ kappa = phi ^ 3)

/-- The capacity-side slope-ratio invariant. -/
def balancedTwoatomCapacitySlopeRatio (_phi p : ℝ) : ℝ :=
  p

/-- The completion identity leaves two admissible branches, but the capacity slope ratio selects
the golden branch and excludes the symmetric `p = 1/2` option. -/
def balancedTwoatomCompletionCapacityBranchSelection (phi : ℝ) : Prop :=
  balancedTwoatomCompletionBranch phi (1 / 2) 4 ∧
    balancedTwoatomCompletionBranch phi (1 / phi) (phi ^ 3) ∧
    (∀ p : ℝ, 1 / 2 < p ∧ p < 1 → p * (1 - p) = 2 * p - 1 → p = 1 / phi) ∧
    balancedTwoatomCapacitySlopeRatio phi (1 / phi) = 1 / phi ∧
    balancedTwoatomCapacitySlopeRatio phi (1 / 2) ≠ 1 / phi

private theorem half_lt_phiInv : (1 / 2 : ℝ) < 1 / Real.goldenRatio := by
  have hsqrt5_nonneg : (0 : ℝ) ≤ Real.sqrt 5 := by positivity
  have hsqrt5_lt_three : Real.sqrt 5 < 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  rw [Real.goldenRatio]
  field_simp
  nlinarith

private theorem phiInv_lt_one : (1 / Real.goldenRatio : ℝ) < 1 := by
  have hsqrt5_gt_one : (1 : ℝ) < Real.sqrt 5 := by
    have hsqrt5_nonneg : (0 : ℝ) ≤ Real.sqrt 5 := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  rw [Real.goldenRatio]
  field_simp
  nlinarith [show (0 : ℝ) ≤ Real.sqrt 5 by positivity]

/-- Paper label: `thm:conclusion-balanced-twoatom-completion-capacity-branch-selection`. The
golden-bias uniqueness theorem identifies the only admissible interior branch, while the
capacity-slope invariant rules out the symmetric branch `p = 1/2`. -/
theorem paper_conclusion_balanced_twoatom_completion_capacity_branch_selection :
    balancedTwoatomCompletionCapacityBranchSelection Real.goldenRatio := by
  refine ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, ?_, rfl, ?_⟩
  · intro p hp hpEq
    exact (paper_conclusion_golden_bias_second_order_uniqueness p hp).mp hpEq |>.1
  · simpa [balancedTwoatomCapacitySlopeRatio] using (ne_of_lt half_lt_phiInv)

end Omega.Conclusion
