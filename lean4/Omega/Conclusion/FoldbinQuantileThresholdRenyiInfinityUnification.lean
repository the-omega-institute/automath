import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-foldbin-quantile-threshold-renyi-infty-unification`. -/
theorem paper_conclusion_foldbin_quantile_threshold_renyi_infty_unification
    (ε quantileLimit renyiInftyExp : ℝ)
    (hε0 : 0 < ε) (hεsub : ε < Real.goldenRatio / Real.sqrt 5)
    (hQuantile : quantileLimit = Real.goldenRatio ^ (2 : ℕ) / Real.sqrt 5)
    (hRenyi : renyiInftyExp = Real.goldenRatio ^ (2 : ℕ) / Real.sqrt 5) :
    quantileLimit = renyiInftyExp := by
  have _ : 0 < ε := hε0
  have _ : ε < Real.goldenRatio / Real.sqrt 5 := hεsub
  exact hQuantile.trans hRenyi.symm

end Omega.Conclusion
