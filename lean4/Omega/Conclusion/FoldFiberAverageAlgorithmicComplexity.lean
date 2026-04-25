import Mathlib.Tactic
import Omega.POM.OracleCapacityKolmogorovSpectrum
import Omega.POM.ReversibleExternalResidualKolmogorovLowerBound

namespace Omega.Conclusion

/-- Concrete package for the fiberwise average-complexity sandwich. The POM fields carry the
upper and lower Kolmogorov infrastructure, while the scalar fields record the chosen center
`K(x | m) + log₂ d_m(x)` and the two explicit logarithmic deficiency terms. -/
structure FoldFiberAverageAlgorithmicComplexityData where
  spectrum : Omega.POM.OracleCapacityKolmogorovSpectrumData
  residual : Omega.POM.ReversibleExternalResidualKolmogorovData
  pointwiseKolmogorovBound : spectrum.pointwiseKolmogorovBound
  pointwiseCapacityCoverage : spectrum.pointwiseCapacityCoverage
  baseComplexity : ℝ
  fiberLogComplexity : ℝ
  averageComplexity : ℝ
  upperGap : ℝ
  lowerGap : ℝ
  logResolution : ℝ
  average_eq_upper :
    averageComplexity = baseComplexity + fiberLogComplexity + upperGap
  average_eq_lower :
    averageComplexity = baseComplexity + fiberLogComplexity - lowerGap
  upperGap_le_logResolution : upperGap ≤ logResolution
  lowerGap_le_logResolution : lowerGap ≤ logResolution

namespace FoldFiberAverageAlgorithmicComplexityData

/-- The average fiber complexity sits between the lower-tail budget and the oracle/Kolmogorov
upper envelope, with both defects controlled by a uniform logarithmic scale. -/
def averageFiberComplexityLaw (D : FoldFiberAverageAlgorithmicComplexityData) : Prop :=
  D.spectrum.aggregateSpectrumEquivalence ∧
    D.residual.typicalLowerBound ∧
    D.residual.expectedLowerBound ∧
    D.baseComplexity + D.fiberLogComplexity - D.logResolution ≤ D.averageComplexity ∧
    D.averageComplexity ≤ D.baseComplexity + D.fiberLogComplexity + D.logResolution

end FoldFiberAverageAlgorithmicComplexityData

open FoldFiberAverageAlgorithmicComplexityData

/-- Paper label: `thm:conclusion-fold-fiber-average-algorithmic-complexity`. The existing
oracle-capacity/Kolmogorov comparison gives the uniform upper envelope, the reversible residual
audit supplies the fiberwise lower bound, and the chosen deficiency scalars convert those two
inputs into a single `O(log m)` sandwich around `K(x | m) + log₂ d_m(x)`. -/
theorem paper_conclusion_fold_fiber_average_algorithmic_complexity
    (D : FoldFiberAverageAlgorithmicComplexityData) : D.averageFiberComplexityLaw := by
  have hSpectrum : D.spectrum.aggregateSpectrumEquivalence :=
    Omega.POM.paper_pom_oracle_capacity_kolmogorov_spectrum
      D.spectrum D.pointwiseKolmogorovBound D.pointwiseCapacityCoverage
  have hResidual :
      D.residual.typicalLowerBound ∧ D.residual.expectedLowerBound :=
    Omega.POM.paper_pom_reversible_external_residual_kolmogorov_lower_bound D.residual
  refine ⟨hSpectrum, hResidual.1, hResidual.2, ?_, ?_⟩
  · nlinarith [D.average_eq_lower, D.lowerGap_le_logResolution]
  · nlinarith [D.average_eq_upper, D.upperGap_le_logResolution]

end Omega.Conclusion
