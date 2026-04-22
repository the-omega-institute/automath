import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.FoldBinGaugeConstantZetaEvenRecoveryLimit

namespace Omega.Folding

open FoldBinGaugeConstantZetaEvenRecoveryData

noncomputable section

/-- Paper label: `thm:fold-bin-gauge-constant-stirling-bernoulli-hierarchy`.
The hierarchy package combines the exact Stirling--Bernoulli decomposition of the normalized
gauge deficiency with the termwise Bernoulli and even-`ζ` recovery already formalized elsewhere. -/
def fold_bin_gauge_constant_stirling_bernoulli_hierarchy_statement : Prop :=
  ∀ D : Omega.Folding.FoldBinGaugeConstantZetaEvenRecoveryData,
    killoFoldBinNormalizedGaugeDeficiency D.C D.m =
        Real.log (2 * Real.pi) + killoFoldBinGaugeDeficiencyMainTerm D.R D.m +
          killoFoldBinGaugeDeficiencyRemainder D.C D.R D.m ∧
      D.bernoulliCoeffRecovered ∧
      D.zetaEvenRecovered

theorem paper_fold_bin_gauge_constant_stirling_bernoulli_hierarchy :
    fold_bin_gauge_constant_stirling_bernoulli_hierarchy_statement := by
  intro D
  refine ⟨?_, ?_, ?_⟩
  · exact (paper_killo_fold_bin_normalized_gauge_deficiency D.C D.R D.m).2
  · exact (paper_fold_bin_gauge_constant_zeta_even_recovery_limit D).1
  · exact (paper_fold_bin_gauge_constant_zeta_even_recovery_limit D).2

end

end Omega.Folding
