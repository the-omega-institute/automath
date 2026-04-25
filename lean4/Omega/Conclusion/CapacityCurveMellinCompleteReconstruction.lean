import Omega.Folding.FoldBinGaugeConstantStirlingBernoulliHierarchy
import Omega.Folding.FoldBinRecover2Pi
import Omega.Folding.FoldNegativeMomentsCapacityMellin

namespace Omega.Conclusion

noncomputable section

/-- Concrete conclusion-level package for capacity-curve Mellin reconstruction: the verified
negative-moment/capacity relation is available for every positive Mellin parameter, and the same
odd-moment channel feeds the existing Stirling--Bernoulli and `2π` reconstruction wrappers. -/
def conclusion_capacity_curve_mellin_complete_reconstruction_statement : Prop :=
  (∀ (m : ℕ) {p : ℝ}, 0 < p → Omega.Folding.FoldNegativeMomentsCapacityMellinStatement m p) ∧
    Omega.Folding.fold_bin_gauge_constant_stirling_bernoulli_hierarchy_statement ∧
    Omega.Folding.fold_bin_recover_2pi_statement

/-- Paper label: `thm:conclusion-capacity-curve-mellin-complete-reconstruction`. -/
theorem paper_conclusion_capacity_curve_mellin_complete_reconstruction :
    conclusion_capacity_curve_mellin_complete_reconstruction_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro m p hp
    exact Omega.Folding.paper_fold_negative_moments_capacity_mellin m hp
  · exact Omega.Folding.paper_fold_bin_gauge_constant_stirling_bernoulli_hierarchy
  · exact Omega.Folding.paper_fold_bin_recover_2pi

end

end Omega.Conclusion
