import Mathlib.Tactic
import Omega.Folding.FoldBinGaugeConstantStirlingBernoulliHierarchy
import Omega.Folding.FoldBinRecover2Pi
import Omega.Folding.FoldNegativeMomentsCapacityMellin

namespace Omega.Conclusion

noncomputable section

/-- Concrete conclusion-level translation package: specialize the existing capacity-curve Mellin
reconstruction at the odd Mellin parameters `p = 2r - 1`, then pair it with the already audited
Stirling--Bernoulli hierarchy and `2π` recovery wrappers. -/
def conclusion_foldpi_euler_mellin_translation_statement : Prop :=
  (∀ (m r : ℕ), 1 ≤ r →
    Omega.Folding.FoldNegativeMomentsCapacityMellinStatement m (2 * (r : ℝ) - 1)) ∧
    Omega.Folding.fold_bin_gauge_constant_stirling_bernoulli_hierarchy_statement ∧
    Omega.Folding.fold_bin_recover_2pi_statement

/-- Paper label: `thm:conclusion-foldpi-euler-mellin-translation`. -/
theorem paper_conclusion_foldpi_euler_mellin_translation :
    conclusion_foldpi_euler_mellin_translation_statement := by
  refine ⟨?_, Omega.Folding.paper_fold_bin_gauge_constant_stirling_bernoulli_hierarchy,
    Omega.Folding.paper_fold_bin_recover_2pi⟩
  intro m r hr
  apply Omega.Folding.paper_fold_negative_moments_capacity_mellin
  have hr_real : (1 : ℝ) ≤ r := by
    exact_mod_cast hr
  nlinarith

end

end Omega.Conclusion
