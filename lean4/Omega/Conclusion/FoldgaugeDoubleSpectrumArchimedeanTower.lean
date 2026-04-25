import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.FoldBinGaugeConstantStirlingBernoulliHierarchy
import Omega.Folding.FoldBinRecover2Pi

namespace Omega.Conclusion

noncomputable section

/-- Paper-facing wrapper for
`thm:conclusion-foldgauge-double-spectrum-archimedean-tower`: the Perron-side recovery of `φ`,
the fold-gauge recovery of `2π`, and the established Bernoulli/even-`ζ` hierarchy together give
the full archimedean tower package used in the paper. -/
def conclusion_foldgauge_double_spectrum_archimedean_tower_statement : Prop :=
  (Real.goldenRatio ^ 2 = Real.goldenRatio + 1) ∧
    Omega.Folding.fold_bin_recover_2pi_statement ∧
    Omega.Folding.fold_bin_gauge_constant_stirling_bernoulli_hierarchy_statement

theorem paper_conclusion_foldgauge_double_spectrum_archimedean_tower :
    conclusion_foldgauge_double_spectrum_archimedean_tower_statement := by
  refine ⟨Real.goldenRatio_sq, Omega.Folding.paper_fold_bin_recover_2pi, ?_⟩
  exact Omega.Folding.paper_fold_bin_gauge_constant_stirling_bernoulli_hierarchy

end

end Omega.Conclusion
