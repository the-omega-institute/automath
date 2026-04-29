import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

universe u

/-- Concrete finite-fiber oracle package for the block threshold collapse.  The allocation fields
are functions on the actual block space, and the certificates identify optimality with the
fiberwise `min` rule and the likelihood-threshold comparison. -/
structure conclusion_foldbin_oracle_block_threshold_collapse_data where
  conclusion_foldbin_oracle_block_threshold_collapse_Block : Type u
  conclusion_foldbin_oracle_block_threshold_collapse_tau : ℝ
  conclusion_foldbin_oracle_block_threshold_collapse_budget : ℕ
  conclusion_foldbin_oracle_block_threshold_collapse_fiberMultiplicity :
    conclusion_foldbin_oracle_block_threshold_collapse_Block → ℕ
  conclusion_foldbin_oracle_block_threshold_collapse_optimalAllocation :
    conclusion_foldbin_oracle_block_threshold_collapse_Block → ℕ
  conclusion_foldbin_oracle_block_threshold_collapse_thresholdAllocation :
    conclusion_foldbin_oracle_block_threshold_collapse_Block → ℕ
  conclusion_foldbin_oracle_block_threshold_collapse_likelihoodRatio :
    conclusion_foldbin_oracle_block_threshold_collapse_Block → ℝ
  conclusion_foldbin_oracle_block_threshold_collapse_likelihoodThreshold : ℝ
  conclusion_foldbin_oracle_block_threshold_collapse_optimal_eq_fiberwise_min :
    ∀ w,
      conclusion_foldbin_oracle_block_threshold_collapse_optimalAllocation w =
        Nat.min
          (conclusion_foldbin_oracle_block_threshold_collapse_fiberMultiplicity w)
          conclusion_foldbin_oracle_block_threshold_collapse_budget
  conclusion_foldbin_oracle_block_threshold_collapse_threshold_eq_fiberwise_min :
    ∀ w,
      conclusion_foldbin_oracle_block_threshold_collapse_thresholdAllocation w =
        Nat.min
          (conclusion_foldbin_oracle_block_threshold_collapse_fiberMultiplicity w)
          conclusion_foldbin_oracle_block_threshold_collapse_budget
  conclusion_foldbin_oracle_block_threshold_collapse_likelihood_threshold_iff :
    ∀ w,
      conclusion_foldbin_oracle_block_threshold_collapse_fiberMultiplicity w ≤
          conclusion_foldbin_oracle_block_threshold_collapse_budget ↔
        conclusion_foldbin_oracle_block_threshold_collapse_likelihoodRatio w ≤
          conclusion_foldbin_oracle_block_threshold_collapse_likelihoodThreshold

namespace conclusion_foldbin_oracle_block_threshold_collapse_data

/-- The optimal oracle allocation can be replaced by the block-threshold allocation, and the
same cut is expressed by the likelihood-ratio threshold. -/
def hasBlockThresholdCollapse
    (D : conclusion_foldbin_oracle_block_threshold_collapse_data) : Prop :=
  (∀ w,
      D.conclusion_foldbin_oracle_block_threshold_collapse_optimalAllocation w =
        D.conclusion_foldbin_oracle_block_threshold_collapse_thresholdAllocation w) ∧
    ∀ w,
      D.conclusion_foldbin_oracle_block_threshold_collapse_fiberMultiplicity w ≤
          D.conclusion_foldbin_oracle_block_threshold_collapse_budget ↔
        D.conclusion_foldbin_oracle_block_threshold_collapse_likelihoodRatio w ≤
          D.conclusion_foldbin_oracle_block_threshold_collapse_likelihoodThreshold

end conclusion_foldbin_oracle_block_threshold_collapse_data

/-- Paper label: `thm:conclusion-foldbin-oracle-block-threshold-collapse`. -/
theorem paper_conclusion_foldbin_oracle_block_threshold_collapse
    (D : conclusion_foldbin_oracle_block_threshold_collapse_data) :
    D.hasBlockThresholdCollapse := by
  refine ⟨?_, D.conclusion_foldbin_oracle_block_threshold_collapse_likelihood_threshold_iff⟩
  intro w
  rw [D.conclusion_foldbin_oracle_block_threshold_collapse_optimal_eq_fiberwise_min w,
    D.conclusion_foldbin_oracle_block_threshold_collapse_threshold_eq_fiberwise_min w]

end Omega.Conclusion
