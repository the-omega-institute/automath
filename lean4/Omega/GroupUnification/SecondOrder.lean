import Omega.GroupUnification.UniversalQuadraticCoefficient

namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for quadratic comparison near the Parry point in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    thm:second-order -/
theorem paper_zero_jitter_second_order
    (fluctuationNormalForm smoothVarianceExpansion fisherQuadraticForm
      relativeEntropyQuadraticExpansion entropyDeficitQuadraticExpansion
      jitterQuadraticExpansion universalRatioTwo goldenMeanSpecialization
      parryPointQuadraticComparison relativeEntropySecondOrder : Prop)
    (hNormalForm : fluctuationNormalForm)
    (hSmooth : fluctuationNormalForm → smoothVarianceExpansion)
    (hFisher : smoothVarianceExpansion → fisherQuadraticForm)
    (hKL : fisherQuadraticForm → relativeEntropyQuadraticExpansion)
    (hEntropy : relativeEntropyQuadraticExpansion → entropyDeficitQuadraticExpansion)
    (hJitter : fisherQuadraticForm → jitterQuadraticExpansion)
    (hRatio :
      entropyDeficitQuadraticExpansion → jitterQuadraticExpansion → universalRatioTwo)
    (hGolden : universalRatioTwo → goldenMeanSpecialization)
    (hComparison : goldenMeanSpecialization → parryPointQuadraticComparison)
    (hRelative : parryPointQuadraticComparison → relativeEntropySecondOrder) :
    smoothVarianceExpansion ∧ entropyDeficitQuadraticExpansion ∧ jitterQuadraticExpansion ∧
      parryPointQuadraticComparison ∧ relativeEntropySecondOrder := by
  obtain ⟨hSmoothExpansion, hFisherForm, _, hEntropyExpansion, hJitterExpansion, hRatioTwo⟩ :=
    paper_zero_jitter_universal_quadratic_coefficient
      fluctuationNormalForm smoothVarianceExpansion fisherQuadraticForm
      relativeEntropyQuadraticExpansion entropyDeficitQuadraticExpansion
      jitterQuadraticExpansion universalRatioTwo hNormalForm hSmooth hFisher hKL hEntropy
      hJitter hRatio
  have hGoldenSpecialization : goldenMeanSpecialization := hGolden hRatioTwo
  have hComparisonNearParry : parryPointQuadraticComparison := hComparison hGoldenSpecialization
  exact
    ⟨hSmoothExpansion, hEntropyExpansion, hJitterExpansion, hComparisonNearParry,
      hRelative hComparisonNearParry⟩

end Omega.GroupUnification
